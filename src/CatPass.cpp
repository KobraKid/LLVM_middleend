#include "llvm/ADT/BitVector.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
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
	 * GEN, KILL, IN, OUT
	 * It also provides functions for adding to these sets, printing the sets,
	 * and retreiving the Instruction to which these sets belong.
	 */
	struct DFA_SET {
	public:
		DFA_SET(Instruction *I): m_inst(I) {}
		void add(int i, int set);
		void add(BitVector *i, int set);
		void print(std::vector<DFA_SET*> *dfa);
		Instruction* getInstruction() const { return m_inst; }
		BitVector* get_gen() { return &m_gen; };
		BitVector* get_kill() { return &m_kill; };
		BitVector* get_in() { return &m_in; };
		BitVector* get_out() { return &m_out; };
		// Set flags
		const static int GEN = 0;
		const static int KILL = 1;
		const static int IN = 2;
		const static int OUT = 3;
	private:
		Instruction *m_inst;
		BitVector m_gen;
		BitVector m_kill;
		BitVector m_in;
		BitVector m_out;
	};

	void DFA_SET::add(int i, int set) {
		switch (set) {
			case GEN:
				if (m_gen.size() < i + 1) {
					m_gen.resize(i + 1);
				}
				m_gen.set(i);
				break;
			case KILL:
				if (m_kill.size() < i + 1) {
					m_kill.resize(i + 1);
				}
				m_kill.set(i);
				break;
			case IN:
				if (m_in.size() < i + 1) {
					m_in.resize(i + 1);
				}
				m_in.set(i);
				break;
			case OUT:
				if (m_out.size() < i + 1) {
					m_out.resize(i + 1);
				}
				m_out.set(i);
				break;
			default:
				errs() << ">>>> Invalid set ID: " << set << "\n";
				break;
		}
	}

	void DFA_SET::add(BitVector *v, int set) {
		for (auto i = 0; i < v->size(); i++) {
			if ((*v)[i]) {
				add(i, set);
			}
		}
	}

	void DFA_SET::print(std::vector<DFA_SET*> *dfa) {
		errs() << "INSTRUCTION: " << *m_inst << "\n";
		/*
		errs() << "***************** GEN\n";
		errs() << "{\n";
		for (auto i = 0; i < m_gen.size(); i++) {
			if (m_gen[i]) {
				errs() << " " << *((*dfa)[i]->getInstruction()) << "\n";
			}
		}
		errs() << "}\n";
		errs() << "**************************************\n";
		errs() << "***************** KILL\n";
		errs() << "{\n";
		for (auto i = 0; i < m_kill.size(); i++) {
			if (m_kill[i]) {
				errs() << " " << *((*dfa)[i]->getInstruction()) << "\n";
			}
		}
		errs() << "}\n";
		errs() << "**************************************\n\n\n\n";
		*/

		errs() << "***************** IN\n";
		errs() << "{\n";
		for (auto i = 0; i < m_in.size(); i++) {
			if (m_in[i]) {
				errs() << " " << *((*dfa)[i]->getInstruction()) << "\n";
			}
		}
		errs() << "}\n";
		errs() << "**************************************\n";
		errs() << "***************** OUT\n";
		errs() << "{\n";
		for (auto i = 0; i < m_out.size(); i++) {
			if (m_out[i]) {
				errs() << " " << *((*dfa)[i]->getInstruction()) << "\n";
			}
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
			DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

			std::vector<DFA_SET*> DFA;
			auto index = 0;
			bool first;

			errs() << "Function \"" << F.getName() << "\" \n";

			// Pass 1: GEN/KILL
			for (auto& B : F) {
				// Skip unreachable code
				if (DT.getNode(&B) == NULL) {
					continue;
				}
				for (auto& I : B) {
					// Store GEN/KILL in this object for each instruction
					DFA_SET* p_dfa = new DFA_SET(&I);
					// We're only interested in Call Instructions
					if (auto callInst = dyn_cast<CallInst>(&I)) {
						auto f_name = callInst->getCalledFunction()->getName();
						// We're only intereset in calls to the CAT API
						auto cat_iter = find(CAT_API::API.begin(), CAT_API::API.end(), f_name);
						if (cat_iter != CAT_API::API.end() && cat_iter != CAT_API::API.begin() + 3) {
							// Add any new, add, sub, or set calls to the instruction's GEN
							p_dfa->add(index, DFA_SET::GEN);
							// Look for any other instructions this one KILLs (and other instructions that KILL this one)
							for (auto i = 0; i < DFA.size(); i++) {
								if (isKilledBy(DFA[i]->getInstruction(), p_dfa->getInstruction())) {
									DFA[i]->add(index, DFA_SET::KILL);
									p_dfa->add(i, DFA_SET::KILL);
								}
							}
						}
					}
					DFA.push_back(p_dfa);
					index++;
				}
			}

			// Pass 2: IN/OUT
			bool out_has_changed = false;
			do {
				index = 0;
				out_has_changed = false;
				for (auto& B : F) {
					// Skip unreachable code
					if (DT.getNode(&B) == NULL) {
						continue;
					}
					first = true;
					for (auto& I : B) {
						auto p_dfa = DFA[index];
						BitVector comp{ *(p_dfa->get_out()) };
						// Generate IN set if this instruction has predecessors
						// First check if this is a BasicBlock's entry point
						if (first) {
							for (auto B : predecessors(&B)) {
								// Find DFA of predecessor BasicBlock's terminator Instruction
								for (auto i = 0; i < DFA.size(); i++) {
									if (DFA[i]->getInstruction() == B->getTerminator()) {
										// Add the OUT set of the predecessor to this Instruction's IN set
										p_dfa->add(DFA[i]->get_out(), DFA_SET::IN);
									}
								}
							}
						}
						// If not, then just get the previous instruction
						else {
							// Add the OUT set of the predecessor to this Instruction's IN set
							p_dfa->add(DFA[index - 1]->get_out(), DFA_SET::IN);
						}
						// Generate OUT set as a function of this Instruction's other sets
						p_dfa->add(p_dfa->get_gen(), DFA_SET::OUT);
						BitVector set_diff{ *(p_dfa->get_in()) };
						set_diff ^= *(p_dfa->get_kill());
						set_diff &= *(p_dfa->get_in());
						p_dfa->add(&set_diff, DFA_SET::OUT);

						if (comp != *(p_dfa->get_out())) {
							out_has_changed = true;
						}

						index++;
						first = false;
					}
				}
			} while (out_has_changed);

			// Print the DFA sets
			for (auto p_dfa : DFA) {
				p_dfa->print(&DFA);
			}

			// Release memory
			for (auto p_dfa : DFA) {
				delete p_dfa;
			}

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
