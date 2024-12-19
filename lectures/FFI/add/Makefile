cadd: 
	gcc -c -o cadd.o cadd.c

add: cadd.o
	ghc --make -main-is Add -o add Add.hs cadd.o

clean: 
	rm -f add *.o *.hi