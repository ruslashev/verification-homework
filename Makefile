all:
	reset
	frama-c -av cycle.c

nr:
	frama-c -av cycle.c

build:
	gcc cycle.c -o cycle
	./cycle

