all: LLParser

LLParser: LLParser.ml
	ocamlc -g -o LLParser LLParser.ml

%.c: %.calc LLParser
	./LLParser -c $< > $@

primes: primes.c
	cc -o primes primes.c

clean:
	rm -f LLParser LLParser.cmi LLParser.cmo
