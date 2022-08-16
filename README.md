# sml-to-coq
A tool that translates SML code to Coq

# Installation
### Sml-to-coq uses:
- [coq 8.12.0](https://coq.inria.fr/download)
- [SML/NJ](https://www.smlnj.org/)
- [Equations](https://github.com/mattam82/Coq-Equations)

### Clone the project:
```
 $ git clone --recurse-submodules https://github.com/meta-logic/sml-to-coq.git
```
### Building the Coq Basis Library
Since most SML programs will make use of some part of `SML's basis library`, we have implemented Coq equivalents to them.
- [coqBasisLib Documantation](https://github.com/meta-logic/sml-to-coq/tree/master/coqBasisLib/doc)

To compile the Coq Basis Library:
1. From the top level directory, go to `coqBasisLib/libs` 
2. Then run: ``` $ make ```

# Using the tool
At the top level directory, run:
```
 $ sml -m sources.cm
```

### Generator
The main function for generating the Coq code is `Generator.generate()` in `generator.sml`. It generates a `.v` file from the passed `.sml` file.
``` 
generate(inputFile, outputFile): string * string -> unit
```


##### For example:
```
Generator.generate("smlCode.sml", "gallinaCode.v"); 
```
Generates the file `galllinaCode.v` from the file `smlCode.sml` . The file  `galllinaCode.v` will be located at the top level directory.

To run `gallinaCode.v` using [coqide](https://coq.inria.fr/download):
1. From the top level go to `coqBasisLib/libs`
2. Then run: ``` $ coqide ```
3. From coqide's GUI open `gallinaCode.v`
4. Run the file

### Convertor
The main function for translating SML code is `Convertor.convert()` in `convertor.sml`. It takes as a parameter a `.sml` file path to the SML program to be translated, and returns the corresponding Gallina AST. 
```
Convertor.convert(inputFile): string -> Gallina.sentence list
```

##### For example:

```
Convertor.convert("smlCode.sml"): 
```
Returns Gallina's AST of the sml code in `smlCode.sml`, and also it prints it.


# Important Directories
- [examples](https://github.com/meta-logic/sml-to-coq/tree/master/examples) : Examples of the translation
- [doc](https://github.com/meta-logic/sml-to-coq/tree/master/doc) : The documentation of the translation
- [coqBasisLib](https://github.com/meta-logic/sml-to-coq/tree/master/coqBasisLib)
- [hamlet](https://github.com/meta-logic/hamlet/tree/836f39ac50121640720be4f642fe2adcfbdac686)
