# Adapted from https://reverseengineering.stackexchange.com/questions/21207/

from ghidra.app.decompiler import DecompInterface
from ghidra.util.task import ConsoleTaskMonitor

# Definitions to make the file compilable.
preamble = """
_Bool pbool(int);

void pact(int);

#define byte char
#define true 1
"""

program = currentProgram  # noqa
decompinterface = DecompInterface()
decompinterface.openProgram(program)
functions = program.getFunctionManager().getFunctions(True)

with open(program.getName()[:-2] + '-decompiled.c', 'w') as handle:
    handle.write(preamble)
    for function in list(functions):
        # These are external functions whose types are not correctly decompiled
        # by Ghidra, so we leave them out (correct definitions above).
        if function.getName() in ['pact', 'pbool']:
            continue

        # decompile each function
        tokengrp = decompinterface.decompileFunction(
            function,
            0,
            ConsoleTaskMonitor()
        )

        handle.write(tokengrp.getDecompiledFunction().getC())
