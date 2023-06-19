# Translator: solidity -> ursus
## Script for generating Ursus project from Everscale solidity project (using ast)


## Dependencies (make sure that you don't have io, system packcges on opam list!):
1. coq-io [git@github.com:Pruvendo/coq-io.git](https://github.com/Pruvendo/coq-io) (automatically installed by ```make install```)
2. coq-json [https://vcs.modus-ponens.com/ton/coq-json](https://github.com/Pruvendo/coq-json) (automatically installed by ```make install```)
3. system [git@github.com:Pruvendo/coq-system.git](https://github.com/Pruvendo/coq-system) (automatically installed by ```make install```)
4. solc-compiler (ethereum )https://docs.soliditylang.org/en/v0.8.17/installing-solidity.html
5. python3 https://www.python.org/downloads/
6. Make
7. coq
8. dune

## Building
```bash
make build
```

## Generate trees and translate 
```bash
python3 tree_generate.py -i path/to/project && python3 tree_translate.py
```
