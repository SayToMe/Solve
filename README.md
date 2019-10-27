# Solve

This library is an interpreter and transpiler of Prolog programming language to F# that provides an additional sweet syntax and strong typing. This project could be used to interpret and migrate existing Prolog code or in educational purposes.
Current Prolog features implemented:
* Basic rules
* Complex rules
* Multiple results
* Unification with different parameter/argument variable names
* Strings and lists
* Custom calls
* Temporary variables
* Recursive calls
* Calc calls by structs
* Lazy execution
* Cut operator
* Not operator
* Prolog code parser

These features are not implemented yet:
* Standard library
* Wild card variables
* Cut operator within same signature (name/arity) facts and rules.

Known bugs:
* Unification is eager/one-directed right now. I.E. `L = [1,2,3], member(1, L)` is not same as `member(1, L), L = [1,2,3]`.

## Requirements

Solve requires a local git installed. You can download git from [Git Downloads](https://git-scm.com/downloads).

Solve requires a .NET Core 3.0 installed. You can download it from [.NET Core 3.0 Downloads](https://dotnet.microsoft.com/download/dotnet-core/3.0).

## Code coverage

[![codecov](https://codecov.io/gh/Qrtic/Solve/branch/master/graph/badge.svg)](https://codecov.io/gh/Qrtic/Solve)

## Build Status

[![Build status](https://ci.appveyor.com/api/projects/status/lskhmawlj7tou52v/branch/master?svg=true)](https://ci.appveyor.com/project/Qrtic/solve/branch/master)

## Maintainer(s)

- [@qrtic](https://github.com/qrtic)
