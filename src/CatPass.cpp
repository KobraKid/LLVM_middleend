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
	struct CAT_API {
	public:
		const static std::vector<std::string> API;
	};
	const std::vector<std::string> CAT_API::API{"CAT_add", "CAT_sub", "CAT_new", "CAT_get", "CAT_set"};
	/*
	 * This struct holds DFA sets for a particular Instruction:
	 * GEN, KILL
	 * It also provides functions for adding to these sets, printing the sets,
	 * and retreiving the Instruction to which these sets belong.
	 */
	struct DFA_SET {
	public:
		DFA_SET(Instruction *I): m_inst(I) {}
		void add(Instruction *I, int set);
		void print();
		Instruction* getInstruction() const { return m_inst; }
		const static int GEN = 0;
		const static int KILL = 1;
	private:
		Instruction *m_inst;
		std::set<Instruction*> m_gen;
		std::set<Instruction*> m_kill;
	};

	void DFA_SET::add(Instruction *I, int set) {
		switch (set) {
			case GEN:
				m_gen.insert(I);
				break;
			case KILL:
				m_kill.insert(I);
				break;
			default:
				errs() << ">>>> Invalid set ID: " << set << "\n";
				break;
		}
	}

	void DFA_SET::print() {
		errs() << "INSTRUCTION: " << *m_inst << "\n";
		errs() << "***************** GEN\n";
		errs() << "{\n";
		for (auto& I : m_gen) {
			errs() << " " << *I << "\n";
		}
		errs() << "}\n";
		errs() << "**************************************\n";
		errs() << "***************** KILL\n";
		errs() << "{\n";
		for (auto& I : m_kill) {
			errs() << " " << *I << "\n";
		}
		errs() << "}\n";
		errs() << "**************************************\n\n\n\n";
	}

	struct CAT : public FunctionPass {
		static char ID;

		CAT() : FunctionPass(ID) {}

		/*
		 * Tests if L is killed by R.
		 */
		bool isKilledBy(Instruction *L, Instruction *R) {
			// Check if R is a call instruction
			if (auto r_callinst = dyn_cast<CallInst>(R)) {
				// Get the Instruction at the first operand of R
				if (auto r_operand = dyn_cast<CallInst>(r_callinst->getArgOperand(0))) {
					// Test if L is the same Instruction as the first operand of R
					if (L == r_operand) {
						return true;
					}
					// Check if L is a call instruction
					if (auto l_callinst = dyn_cast<CallInst>(L)) {
						// Get the Instruction at the first operand of L
						if (auto l_operand = dyn_cast<CallInst>(l_callinst->getArgOperand(0))) {
							// Test if the first operand of L is the same Instruction as the first operand of R
							if (l_operand == r_operand) {
								return true;
							}
						}
					}
				}
			}
			return false;
		}

		// This function is invoked once at the initialization phase of the compiler
		// The LLVM IR of functions isn't ready at this point
		bool doInitialization (Module &M) override {
			return false;
		}

		// This function is invoked once per function compiled
		// The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
		bool runOnFunction (Function &F) override {
			// DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

			std::vector<DFA_SET*> DFA;

			errs() << "Function \"" << F.getName() << "\" \n";

			for (auto& B : F) {
				// Skip unreachable code
				// if (DT.getNode(&B) == NULL) {
				// 	continue;
				// }
				for (auto& I : B) {
					// Store GEN/KILL in this object for each instruction
					DFA_SET* p_dfa = new DFA_SET(&I);
					// We're only interested in Call Instructions
					if (auto callInst = dyn_cast<CallInst>(&I)) {
						auto f_name = callInst->getCalledFunction()->getName();
						// We're only intereset in calls to the CAT API
						auto i = find(CAT_API::API.begin(), CAT_API::API.end(), f_name);
						if (i != CAT_API::API.end() && i != CAT_API::API.begin() + 3) {
							// Add any new, add, sub, or set calls to the instruction's GEN
							p_dfa->add(&I, DFA_SET::GEN);
							// Look for any other instructions this one KILLs (and other instructions that KILL this one)
							for (auto p_other : DFA) {
								if (isKilledBy(p_other->getInstruction(), p_dfa->getInstruction())) {
									p_other->add(p_dfa->getInstruction(), DFA_SET::KILL);
									p_dfa->add(p_other->getInstruction(), DFA_SET::KILL);
								}
							}
						}
					}
					DFA.push_back(p_dfa);
				}
			}
			for (auto p_dfa : DFA) {
				p_dfa->print();
				delete p_dfa;
			}

			return false;
		}

		// We don't modify the program, so we preserve all analyses.
		// The LLVM IR of functions isn't ready at this point
		void getAnalysisUsage(AnalysisUsage &AU) const override {
			// AU.addRequired<DominatorTreeWrapperPass>();
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
