/// A parser which produces values of type T
struct Parser<T> {
  /// The actual parsing function.
  /// Since we may need to explore multiple possibilities,
  /// we return an array of possible parses.
  /// For example, an optional parser of type Parser<T?>
  /// may return (nil, input) as one possibility where
  /// no value was parsed and also (value, some proper suffix) to indicate 
  /// another possibility where a value was parsed
  let run: (ArraySlice<Character>) -> [(T, ArraySlice<Character>)]
}

extension Parser {
  /// Runs the parser on a given string and produces the
  /// longest match. For printing convenience, this 
  /// produces T instead of T?
  func run(on str: String) -> T {
    let results = self.run(Array(str)[...])
    // Return the result with the most input consumed
    return results.min(by: { $0.1.count < $1.1.count })!.0
  }
}

/// Runs 'parser' and feeds the result to the function 'next'
func bind<T, R>(_ parser: Parser<T>, _ next: @escaping (T) -> Parser<R>) -> Parser<R> {
  Parser { 
    (input) -> [(R, ArraySlice<Character>)] in
      parser.run(input).flatMap { (result) -> [(R, ArraySlice<Character>)] in
        let (match, rest) = result
        return next(match).run(rest)
      }
  }
}

extension Parser {
  /// Changes the value returned by the parser 
  func map<R>(_ f: @escaping (T) -> R) -> Parser<R> {
    Parser<R> { input in self.run(input).map { (v, restInput) in (f(v), restInput) } }
  }
}

func map<T, R>(_ parser: Parser<T>, _ f: @escaping (T) -> R) -> Parser<R> {
  parser.map(f)
}

/// A parser which consumes no input and always succeeds
func succeed<T>(_ value: T) -> Parser<T> {
  Parser { input in [(value, input)] }
}

/// A parser which always fails
func fail<T>() -> Parser<T> {
  Parser { _ in [] }
}

/// Ignores the value returned by the parser
func ignore<T>(_ parser: Parser<T>) -> Parser<()> {
  parser.map { _ in () }
}

/// Succeeds iff we have reached the end of the input
let eof: Parser<()> = Parser { input in (input.isEmpty ? succeed(()) : fail()).run(input) }

/// Consumes characters while 'predicate' is true
func satisfies(_ predicate: @escaping (Character) -> Bool) -> Parser<Character> {
  Parser { input in 
      if let firstChar = input.first, predicate(firstChar) {
        return [(firstChar, input.dropFirst())]
      } else {
        return []
      }
  }  
}

/// Chooses from a list of alternatives
func oneOf<T>(_ choices: [Parser<T>]) -> Parser<T> {
  Parser { input in 
      choices.flatMap { $0.run(input) }
  }
}

extension Parser {
  /// Postfix version of 'oneOf' for convenience
  func or(_ alternative: Parser<T>) -> Parser<T> {
    oneOf([self, alternative])
  }
}

/// Matches one specific character
func char(_ c: Character) -> Parser<Character> {
  satisfies { c == $0 }
}

/// Matches a specific string
func string(_ str: String) -> Parser<String> {
  str.reversed().reduce(succeed(str)) { next, c in 
    chain {
      char(c)
      next 
    }
  }
}

/// Consumes characters while 'predicate' is true,
/// and returns the result as a string for convenience
func takeWhile(_ predicate: @escaping (Character) -> Bool) -> Parser<String> {
  Parser { input in 
      let idx = input.firstIndex(where: { !predicate($0) }) ?? input.endIndex
      return [(String(input[..<idx]), input[idx...])]
  }
}

/// A parser which either runs 'parser' or doesn't consume input
func optionally<T>(_ parser: Parser<T>) -> Parser<T?> {
  parser.map(Optional.some).or(succeed(.none))
}

/// Convenience form of 'optionally' which lets you specify the type directly
func optionally<T>(_ _: T.Type, _ parser: Parser<T>) -> Parser<T?> {
  optionally(parser)
}

/// The equivalent of Kleene star, repeatedly applies 'parser'
/// and collects the results
func zeroOrMore<T>(_ parser: Parser<T>) -> Parser<[T]> {
  Parser { input in 
      var results: [([T], ArraySlice<Character>)] = [([], input)]

      parser.run(input).forEach {
        let (elem, rest) = $0
        for (elems, rest) in zeroOrMore(parser).run(rest) { 
          results.append(([elem] + elems, rest))
        }
      }

      return results 
  }
}

/// The equivalent of + in regex. 
/// Runs one or more times, and collects the results
func oneOrMore<T>(_ parser: Parser<T>) -> Parser<[T]> {
  return chain {
    let first = parser 
    let rest = zeroOrMore(parser)
    succeed([first] + rest)
  }
}

/// Does 'parser' exactly 'times' many times 
func exactly<T>(times: Int, _ parser: Parser<T>) -> Parser<[T]> {
  if times == 0 {
    return succeed([])
  } else {
    return chain {
      let elem = parser 
      let rest = exactly(times: times - 1, parser)
      // for non-quadratic performance, we would instead
      // build this in reverse order and then 
      // have a wrapper which reverses
      succeed([elem] + rest)
    }
  }
}

/// Bounded quantification
func atMost<T>(times: Int, _ parser: Parser<T>) -> Parser<[T]> {
  if times == 0 {
    return succeed([])
  } else {
    let takeOne: Parser<[T]> = chain {
      let elem = parser 
      let rest = atMost(times: times - 1, parser)
      succeed([elem] + rest)
    }

    return takeOne.or(succeed([]))
  }
}

/// Parses a range of possible repetitions 
func between<T>(_ lowerBound: Int, and upperBound: Int, _ parser: Parser<T>) -> Parser<[T]> {
  assert(upperBound >= lowerBound);

  return chain {
    let initial = exactly(times: lowerBound, parser)
    let rest = atMost(times: upperBound - lowerBound, parser)
    succeed(initial + rest)
  }
}

// let aabb: Parser<(Int, Int)> = bind(zeroOrMore(char("A"))) {
//   let Acount = $0.count 
//   return bind(zeroOrMore(char("B"))) {
//     let Bcount = $0.count 
//     return bind(eof) { _ in 
//       return succeed((Acount, Bcount))
//     }
//   }
// }

// print(aabb(Array("AAABB")[...]))

// let e = chain { 
//   let first = parser 
//   let rest = zeroOrMore(parser)
//   succeed([first] + rest)
// }

// Semantics: 
// es ~> es' ⊢ chain { e1; rest } ~> bind(e1, { _ in es' })
//           ⊢ chain { e } ~> e
// es ~> es' ⊢ chain { let p = e1 ; es } ~> bind(e1, { let p = $0; return es' })
// chain { let p = e } ~> error: Chain cannot end with binding

// let aabb: Parser<(Int, Int)> = chain {
//   let Acount = zeroOrMore(char("A")).map { $0.count }
//   let BCount = zeroOrMore(char("B")).map { $0.count }
//   succeed((Acount, Bcount))
// }

let foo: Parser<(Int, Int)> = chain {
  let a = zeroOrMore(char("A"))
  let b = zeroOrMore(char("B"))
  eof
  succeed((a.count, b.count))
}

print(foo.run(on: "AAAABBB"))

let iToS = { Int($0)! }

let number: Parser<Int> = chain {
  let n = takeWhile({ $0.isWholeNumber }).map(iToS)
  skipSpaces
  string("cyz")
  eof
  succeed(n)
}

print("Running number test")
// deferences nullptr for some reason 
// print(number.run(on: "1234 cyz"))

let skipSpaces = ignore(takeWhile({ $0.isWhitespace }))

let unicodeScalar: Parser<UnicodeScalar> = 
  between(4, and: 6, satisfies({ $0.isHexDigit }))
    .map { UnicodeScalar(UInt32(String($0), radix: 16)!)! }

let unicodeData: Parser<(UnicodeScalar, UnicodeScalar?)> = chain {
  let scalarStart = unicodeScalar
  let scalarEnd: UnicodeScalar? = optionally(chain {
    string("..")
    unicodeScalar
  })

  succeed((scalarStart, scalarEnd))
}

print(unicodeData.run(on: "0600..0605 ; "))

let cryptos = oneOf(["bitcoin", "dogecoin", "etherium"].map(string))

// Generic chain examples
func bind<T, R>(_ v: [T], _ f: (T) -> [R]) -> [R] {
  v.flatMap(f)
}

let pairs: [(Int, Int)] = chain {
  let x = [1,2,3,4,5]
  let y = [1,2,3,4,5]
  [(x, y)]
}

print(pairs)
