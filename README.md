# sml-to-coq
A tool that translates SML code to Coq

# Installation
### Sml-to-coq uses:
- [coq 8.12.0](https://coq.inria.fr/download)
- [SML/NJ](https://www.smlnj.org/)
- [Equations](https://github.com/mattam82/Coq-Equations)

### Clone the project:
```
 $ git clone https://github.com/meta-logic/sml-to-coq.git
```

### Building the coqLibraries
Since most SML programs will make use of some part of `SML's basis library`, we have implemented Coq equivalents to them.
- [coqLibraries Documantation](https://github.com/meta-logic/sml-to-coq/tree/sml-to-coq-with-hamlet/coqLibraries/doc)

To compile the coqLibraries:
1. From the top level directory, go to `coqLibraries/libs` 
2. Then run: ``` $ make ```

# Using the tool
At the top level directory, run:
```
 $ sml -m sources.cm
```

### Generator
The main function for generating the Coq code is `Generator.generate()` in `generator.sml`. 
``` 
generate(inputFile, outputFile): string * string -> unit
```
It generates a `.v` file named `outputFile` from the passed `.sml` file named `inputFile`.

For example:
```
Generator.generate("smlCode.sml", "gallinaCode.v"); 
```
will generate the file `galllinaCode.v` from the file `smlCode.sml` . The file  `galllinaCode.v` will be located at the top level directory.

To run `gallinaCode.v` using [coqide](https://coq.inria.fr/download):
1. From the top level go to `coqLibraries/libs`
2. Then run: ``` $ coqide ```
3. From coqide's GUI open `gallinaCode.v`
4. Run the file

### Convertor
The main function for translating SML code is `Convertor.convert()` in `convertor.sml`. 
```
Generator.generate(inputFile): string -> Gallina.sentence list
```
It takes as a parameter a `.sml` file path to the SML program to be translated, and returns the corresponding Gallina AST. 

For example:
```
Convertor.convert("smlCode.sml"): 
```
Returns Gallina's AST of the sml code in `smlCode.sml`, and also it prints it.
