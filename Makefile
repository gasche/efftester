build:
	dune build src/effmain.exe

exec:
	dune exec src/effmain.exe

clean:
	dune clean
	rm -f testdir/test.{ml,o,cmi,cmo,cmx} testdir/{byte,native,byte.out,native.out}

format:
	dune build @fmt --auto-promote