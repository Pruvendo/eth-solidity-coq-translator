all: build

install:
	cd ../   		&& git clone git@vcs.modus-ponens.com:ton/io.git
	cd ../io 		&& opam install . -y
	cd ../   		&& git clone git@vcs.modus-ponens.com:ton/system.git
	cd ../system 	&& opam install . -y
	cd ../ 			&& git clone git@vcs.modus-ponens.com:ton/coq-json.git
	cd ../coq-json 	&& opam install . -y

build:

	time (dune build -j 4 && cd _build/default && ocamlbuild -verbose 2 -tag 'optimize(3)' -j 1 main.native -use-ocamlfind -package io-system && echo "Installed\n")

clean:
	dune clean && rm -rf translated/ trees/ 