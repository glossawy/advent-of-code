SOLUTION_SOURCE:=solution.sml
SOLUTION_TARGET:=solution.tmp.sml
OUTPUT:=solution

ML_BUILD:=mlton
BUILD_ARGS:=-output $(OUTPUT)

ENTRY_POINT='val _ = main (CommandLine.name (), CommandLine.arguments ())'

solution: $(SOLUTION_SOURCE)
	cp $(SOLUTION_SOURCE) $(SOLUTION_TARGET)
	echo $(ENTRY_POINT) >> $(SOLUTION_TARGET)
	$(ML_BUILD) $(BUILD_ARGS) $(SOLUTION_TARGET)
	rm $(SOLUTION_TARGET)

.PHONY: clean

clean:
	rm -f $(OUTPUT)
