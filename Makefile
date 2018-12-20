cz : Main.idr Lib.idr Minimax.idr Utils.idr
	idris -o cz Main.idr

.PHONY: clean
clean : FORCE
	rm -f *.ibc cz

.PHONY: clean

FORCE:
