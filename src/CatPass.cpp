#include "llvm/ADT/BitVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

namespace {
	/// <summary>
	/// This struct holds a list of CAT API function names.
	/// </summary>
	struct CAT_API {
	public:
		const static std::vector<std::string> API;
	};
	const std::vector<std::string> CAT_API::API{ "CAT_add", "CAT_sub", "CAT_new", "CAT_get", "CAT_set" };

	/// A pointer to the Module for use in IR building
	Module* mod;

	/// <summary>
	/// This struct holds DFA sets for a particular <c>Instruction</c>:
	/// <para>GEN, KILL, IN, OUT</para>
	/// It also provides functions for adding to these sets
	/// and retreiving the <c>Instruction</c> to which these sets belong.
	/// </summary>
	struct DFA_SET {
	public:
		DFA_SET(Instruction* I) : m_inst(I) {}
		Instruction* getInstruction() const {
			return m_inst;
		}
		BitVector* get_gen() {
			return &m_gen;
		};
		BitVector* get_kill() {
			return &m_kill;
		};
		BitVector* get_in() {
			return &m_in;
		};
		BitVector* get_out() {
			return &m_out;
		};
		// Convenience functions to add Instructions to SETs
		void add(const int i, const int set);
		void add(const BitVector* i, const int set);
		// SET modification flags
		const static int GEN{ 0 };
		const static int KILL{ 1 };
		const static int IN{ 2 };
		const static int OUT{ 3 };
	private:
		Instruction* m_inst;
		// SETs
		BitVector m_gen;
		BitVector m_kill;
		BitVector m_in;
		BitVector m_out;
	};

	/// <summary>Adds an <c>Instruction</c> to a SET.</summary>
	/// <param name='i'>The index of the <c>Instruction</c> to be added.</param>
	/// <param name='set'>A flag indicating the destination SET.</param>
	void DFA_SET::add(const int i, const int set) {
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

	/// <summary>Adds one SET to another SET.</summary>
	/// <param name='v'><c>BitVector</c> SET to be integrated.</param>
	/// <param name='set'>A flag indicating the destination SET.</param>
	void DFA_SET::add(const BitVector* v, const int set) {
		for (auto i = 0; i < v->size(); i++) {
			if ((*v)[i]) {
				add(i, set);
			}
		}
	}

	struct CAT : public FunctionPass {
		static char ID;

		CAT() : FunctionPass(ID) {}

		/// <summary>Tests if an <c>Instruction</c> is killed by another <c>Instruction</c>.</summary>
		/// <param name='L'>A potentially killed <c>Instruction</c>.</param>
		/// <param name='R'>An <c>Instruction</c> that may kill <c>L</c>.</param>
		/// <returns>true if <c>L</c> is killed by <c>R</c>, false otherwise.</returns>
		bool isKilledBy(const Instruction* L, const Instruction* R) {
			// Check if R is a call instruction
			if (auto r_callinst = dyn_cast<CallInst>(R)) {
				// Return false if R is not a CAT API call
				if (find(CAT_API::API.begin(), CAT_API::API.end(), r_callinst->getCalledFunction()->getName()) == CAT_API::API.end()) { return false; }
				// Get the Instruction at the first operand of R
				if (auto r_operand = dyn_cast<CallInst>(r_callinst->getArgOperand(0))) {
					// Test if L is the same Instruction as the first operand of R
					if (L == r_operand) {
						return true;
					}
					// Check if L is a call instruction
					if (auto l_callinst = dyn_cast<CallInst>(L)) {
						// Return false if L is not a CAT API call
						if (find(CAT_API::API.begin(), CAT_API::API.end(), l_callinst->getCalledFunction()->getName()) == CAT_API::API.end()) { return false; }
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

		/// <summary>Tests if an <c>Instruction</c> (re)defines a <c>Value</c> to a constant value.</summary>
		/// <param name='L'>A potential definition <c>Instruction</c>.</param>
		/// <param name='R'>A <c>Value</c> to be tested.</param>
		/// <returns>A pointer to the value <c>R</c> is set to, or <c>nullptr</c> if <c>L</c> does not (re)define <c>R</c>.</returns>
		ConstantInt* definesAsConstant(const Instruction* L, const Value* R) {
			// Try to cast L to a CAT API call
			if (auto callInst = dyn_cast<CallInst>(L)) {
				// Initial definition of a CAT variable
				//  %1 = tail call i8* @CAT_new(i64 5) #3
				if (
					callInst->getCalledFunction()->getName() == "CAT_new" &&
					callInst == R &&
					isa<ConstantInt>(callInst->getArgOperand(0))
					) {
					return cast<ConstantInt>(callInst->getArgOperand(0));
				}
				// Redefinition of a CAT variable
				//  tail call void @CAT_set(i8* %1, i64 42) #3
				if (
					callInst->getCalledFunction()->getName() == "CAT_set" &&
					callInst->getArgOperand(0) == R &&
					isa<ConstantInt>(callInst->getArgOperand(1))
					) {
					return cast<ConstantInt>(callInst->getArgOperand(1));
				}
			}
			return nullptr;
		}

		/// <summary>Tests if an <c>Instruction</c> (re)defines a <c>Value</c>.</summary>
		/// <param name='L'>A potential definition <c>Instruction</c>.</param>
		/// <param name='R'>A <c>Value</c> to be tested.</param>
		/// <returns>true if <c>L</c> (re)defines <c>R</c>, false otherwise.</returns>
		bool defines(const Instruction* L, const Value* R) {
			// Try to cast L to a CAT API call
			if (auto callInst = dyn_cast<CallInst>(L)) {
				auto f_name = callInst->getCalledFunction()->getName();
				// Initial definition of a CAT variable
				//  %1 = tail call i8* @CAT_new(i64 5) #3
				if (f_name == "CAT_new" && callInst == R) {
					return true;
				}
				// Redefinitions of a CAT variable
				//  tail call void @CAT_set(i8* %1, i64 42) #3
				//  tail call void @CAT_add(i8* %3, i8* %3, i8* %3) #3
				if ((f_name == "CAT_set" || f_name == "CAT_add" || f_name == "CAT_sub") && callInst->getArgOperand(0) == R) {
					return true;
				}
			}
			return false;
		}

		// This function is invoked once at the initialization phase of the compiler
		// The LLVM IR of functions isn't ready at this point
		bool doInitialization(Module& M) override {
			mod = &M; // save the module
			return false;
		}

		// This function is invoked once per function compiled
		// The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
		bool runOnFunction(Function& F) override {
			// Used to keep track of whether our pass has modified anything
			bool has_modified_code{ false };
			// Used to check for unreachable code
			DominatorTree& DT{ getAnalysis<DominatorTreeWrapperPass>().getDomTree() };
			// Used to hold GEN/KILL/IN/OUT SETs for each Instruction
			std::vector<DFA_SET*> DFA;

			// Reusable index variable
			auto index{ 0 };
			// Reusable context variable
			auto& ctx{ F.getContext() };

			/* Pass 1: GEN/KILL */
			for (auto& B : F) {
				// Skip unreachable code
				if (DT.getNode(&B) == NULL) { continue; }

				for (auto& I : B) {
					// Store GEN/KILL in this object for each instruction
					DFA_SET* p_dfa{ new DFA_SET(&I) };
					// We're only interested in Call Instructions
					if (auto callInst = dyn_cast<CallInst>(&I)) {
						// We're only intereset in calls to the CAT API
						auto cat_iter{ find(CAT_API::API.begin(), CAT_API::API.end(), callInst->getCalledFunction()->getName()) };
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

			/* Pass 2: IN/OUT */
			bool first{ true };
			bool out_has_changed{ false };
			do {
				index = 0;
				out_has_changed = false;
				for (auto& B : F) {
					// Skip unreachable code
					if (DT.getNode(&B) == NULL) { continue; }

					first = true;
					for (auto& I : B) {
						auto p_dfa{ DFA[index] };
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

			/* Pass 3: Constant Propagation, Constant Folding */
			index = 0;
			std::map<Instruction*, Value*> propagations;
			std::map<Instruction*, int> foldings;
			for (auto& B : F) {
				// Skip unreachable code
				if (DT.getNode(&B) == NULL) { continue; }

				for (auto& I : B) {
					auto p_dfa{ DFA[index] };
					// We're only interested in Call Instructions
					if (auto callInst = dyn_cast<CallInst>(p_dfa->getInstruction())) {
						auto f_name{ callInst->getCalledFunction()->getName() };
						auto cat_iter{ find(CAT_API::API.begin(), CAT_API::API.end(), f_name) };
						/* Constant Propagation */
						// We're only interested in calls to CAT_new, CAT_get, and CAT_set
						if (cat_iter != CAT_API::API.end() && cat_iter > CAT_API::API.begin() + 1) {
							// Check each argument operand (except arg 0 of CAT_set, it shouldn't become a constant)
							for (int arg = (f_name == "CAT_set" ? 1 : 0); arg < callInst->getNumArgOperands(); arg++) {
								bool can_prop{ true };
								bool valset{ false };
								ConstantInt* val{ nullptr };
								// Iterate through the IN set
								for (int i = 0; i < p_dfa->get_in()->size(); i++) {
									// Check if the instruction in the IN set defines the argument
									if ((*(p_dfa->get_in()))[i]) {
										if (auto c_val = definesAsConstant(DFA[i]->getInstruction(), callInst->getArgOperand(arg))) {
											auto in_callInst{ cast<CallInst>(DFA[i]->getInstruction()) };
											auto op{ in_callInst->getCalledFunction()->getName() == "CAT_new" ? 0 : 1 };
											// Ensure all reaching definitions set v to the same constant c
											if (!valset) {
												valset = true;
												val = c_val;
											}
											else if (val->getSExtValue() != c_val->getSExtValue()) {
												can_prop = false;
												goto CONST_PROP;
											}
										}
										else if (defines(DFA[i]->getInstruction(), callInst->getArgOperand(arg))) {
											// A definition was not constant
											can_prop = false;
											goto CONST_PROP;
										}
									}
								}
								CONST_PROP:
								if (can_prop && valset) {
									// The constant propagation is valid, all reaching definitions are the same constant value
									propagations.insert(std::pair<Instruction*, Value*>(callInst, val));
								}
							}
						}
						/* Constant Folding */
						bool both_consts{ true };
						bool val1set{ false };
						bool val2set{ false };
						int val1{ 0 };
						int val2{ 0 };
						// We're only interested in calls to CAT_add and CAT_sub
						if (f_name != "CAT_add" && f_name != "CAT_sub") { goto CONST_FOLD; }
						errs() << *callInst;
						// Check both args 1 and 2
						for (auto arg = 1; arg <= 2; arg++) {
							// Iterate through the IN set
							for (int i = 0; i < p_dfa->get_in()->size(); i++) {
								// Check if the instruction in the IN set defines the argument
								if ((*(p_dfa->get_in()))[i]) {
									errs() << "\n\t" << *(DFA[i]->getInstruction()) << "\n\t> ";
									if (auto c_val = definesAsConstant(DFA[i]->getInstruction(), callInst->getArgOperand(arg))) {
										errs() << "defines callInst's arg " << arg << " as a constant";
										// Ensure all reaching definitions set v to the same constant c
										switch (arg) {
										case 1:
											if (!val1set) {
												val1 = c_val->getSExtValue();
												val1set = true;
											}
											else if (val1 != c_val->getSExtValue()) {
												both_consts = false;
												goto CONST_FOLD;
											}
											break;
										case 2:
											if (!val2set) {
												val2 = c_val->getSExtValue();
												val2set = true;
											}
											else if (val2 != c_val->getSExtValue()) {
												both_consts = false;
												goto CONST_FOLD;
											}
											break;
										}
									}
									else if (defines(DFA[i]->getInstruction(), callInst->getArgOperand(arg))) {
										errs() << "does not define callInst's arg " << arg << "  as a constant";
										// A definition was not constant
										both_consts = false;
										goto CONST_FOLD;
									}
									else errs() << "does not define callInst's arg " << arg;
								}
							}
						}
						errs() << "\n";
						CONST_FOLD:
						if (both_consts && val1set && val2set) {
							// The constant folding is valid, both operands are constants
							errs() << "> Folding to " << "CAT_set(" << (f_name == "CAT_add" ? val1 + val2 : val1 - val2) << ")\n";
							foldings.insert(std::pair<Instruction*, int>(callInst, (f_name == "CAT_add" ? val1 + val2 : val1 - val2)));
						}
					}
					index++;
				}
			}

			// Go through the mapping of constant propagations and do them
			for (auto prop_iter = propagations.begin(); prop_iter != propagations.end(); prop_iter++) {
				BasicBlock::iterator ii(prop_iter->first);
				ReplaceInstWithValue(prop_iter->first->getParent()->getInstList(), ii, prop_iter->second);
				has_modified_code = true;
			}

			// Go through the mapping of constant foldings and do them
			for (auto fold_iter = foldings.begin(); fold_iter != foldings.end(); fold_iter++) {
				IRBuilder<> builder(fold_iter->first->getParent());
				FunctionCallee f{
					mod->getOrInsertFunction(
						/* function name */
						"CAT_set",
						/* return type */
						Type::getVoidTy(ctx),
						/* args */
						PointerType::get(IntegerType::get(ctx, 8), 0),
						IntegerType::get(ctx, 64)
						)
				};
				std::vector<Value*> params{
					/* param 0: CAT variable */
					cast<CallInst>(fold_iter->first)->getArgOperand(0),
					/* param 1: int */
					ConstantInt::get(ctx, APInt(64, fold_iter->second, true))
				};
				ReplaceInstWithInst(fold_iter->first, CallInst::Create(f, params));
				has_modified_code = true;
			}

			// Release memory
			for (auto p_dfa : DFA) { delete p_dfa; }

			return has_modified_code;
		}

		// We don't modify the program, so we preserve all analyses.
		// The LLVM IR of functions isn't ready at this point
		void getAnalysisUsage(AnalysisUsage& AU) const override {
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.setPreservesAll();
		}
	};
}

// Register this pass to `opt`
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Register this pass to `clang`
static CAT* _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
	[](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
		if (!_PassMaker) { PM.add(_PassMaker = new CAT()); }
	});                                                  // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
	[](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
		if (!_PassMaker) { PM.add(_PassMaker = new CAT()); }
	});                                                   // ** for -O0
