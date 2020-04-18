#include "llvm/Pass.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {
	struct CAT : public FunctionPass {
		static char ID;

		CAT() : FunctionPass(ID) {}

		// This function is invoked once at the initialization phase of the compiler
		// The LLVM IR of functions isn't ready at this point
		bool doInitialization (Module &M) override {
			return false;
		}

		// This function is invoked once per function compiled
		// The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
		bool runOnFunction (Function &F) override {
			int c_add = 0;
			int c_sub = 0;
			int c_new = 0;
			int c_get = 0;
			int c_set = 0;
			std::string c_add_name = "CAT_add";
			std::string c_sub_name = "CAT_sub";
			std::string c_new_name = "CAT_new";
			std::string c_get_name = "CAT_get";
			std::string c_set_name = "CAT_set";
			std::string f_name;

			DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

			for (auto& B : F) {
				if (DT.getNode(&B) == NULL) {
					continue;
				}
				for (auto& I : B) {
					if (isa<CallInst>(I)) {
						CallInst *callInst = cast<CallInst>(&I);
						f_name = callInst->getCalledFunction()->getName();
						if (f_name.compare(c_add_name) == 0) { c_add++; }
						else if (f_name.compare(c_sub_name) == 0) { c_sub++; }
						else if (f_name.compare(c_new_name) == 0) { c_new++; }
						else if (f_name.compare(c_get_name) == 0) { c_get++; }
						else if (f_name.compare(c_set_name) == 0) { c_set++; }
					}
				}
			}

			if (c_add > 0) { errs() << "H1: \"" << F.getName() << "\": CAT_add: " << c_add << "\n"; }
			if (c_sub > 0) { errs() << "H1: \"" << F.getName() << "\": CAT_sub: " << c_sub << "\n"; }
			if (c_get > 0) { errs() << "H1: \"" << F.getName() << "\": CAT_get: " << c_get << "\n"; }
			if (c_new > 0) { errs() << "H1: \"" << F.getName() << "\": CAT_new: " << c_new << "\n"; } // This should be moved up according to the reference sheet
			if (c_set > 0) { errs() << "H1: \"" << F.getName() << "\": CAT_set: " << c_set << "\n"; }
			return false;
		}

		// We don't modify the program, so we preserve all analyses.
		// The LLVM IR of functions isn't ready at this point
		void getAnalysisUsage(AnalysisUsage &AU) const override {
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.setPreservesAll();
		}
	};
}

// Register this pass to `opt`
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Register this pass to `clang`
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
                                        [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
                                        if(!_PassMaker) { PM.add(_PassMaker = new CAT());}
	});                                                  // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
                                        [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
                                        if(!_PassMaker) { PM.add(_PassMaker = new CAT()); }
	});                                                   // ** for -O0
