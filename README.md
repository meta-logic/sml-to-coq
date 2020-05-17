# sml-to-coq

A tool that translates SML code to Coq

## How to use

At the top level directory, run:

```
sml -m sources.cm
```

The main function for translating SML code is `Convertor.convert()` in `convertor.sml`. It takes as a parameter the SML program to be translated as a string, and returns the corresponding Gallina AST. Its type is `string -> Gallina.sentence list`. A list of `Gallina.sentence` is returned in case the SML code is composed of several expressions (e.g. separated by a `;`).

For example:

```
Convertor.convert("val x = 4; val y = 2;");
```
