SOLUTION_SOURCE:=solution.sml
COMPILE_SOURCE:=solution.mlb
SOLUTION_TARGET:=solution.tmp.sml
COMPILE_TARGET:=solution.tmp.mlb
OUTPUT:=solution

ML_BUILD:=mlton
BUILD_ARGS:=-output $(OUTPUT)

ENTRY_POINT='val _ = main (CommandLine.name (), CommandLine.arguments ())'

solution: $(SOLUTION_SOURCE)
	make clean
	# Create Temporary Build Files
	cp $(SOLUTION_SOURCE) $(SOLUTION_TARGET)
	cp $(COMPILE_SOURCE) $(COMPILE_TARGET)
	# Inject entry point into source and ml basis file
	echo $(ENTRY_POINT) >> $(SOLUTION_TARGET)
	echo $(SOLUTION_TARGET) >> $(COMPILE_TARGET)
	# Do Build
	$(ML_BUILD) $(BUILD_ARGS) $(COMPILE_TARGET)
	# Cleanup temporary build files
	rm $(SOLUTION_TARGET) && rm $(COMPILE_TARGET)

.PHONY: clean run

run:
	printf "$(shell basename $(CURDIR)) Part 1: "
	./solution part1 | tail -n1
	printf "$(shell basename $(CURDIR)) Part 2: "
	./solution part2 | tail -n1

clean:
	rm -f $(OUTPUT) $(SOLUTION_TARGET) $(COMPILE_TARGET)
