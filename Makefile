all: LLParser primes

LLParser: LLParser.ml
	ocamlc -o LLParser LLParser.ml

%.c: %.calc LLParser
	./LLParser -c < $< > $@

primes: primes.c
	cc -o primes primes.c

clean:
	rm -f LLParser LLParser.cmi LLParser.cmo
