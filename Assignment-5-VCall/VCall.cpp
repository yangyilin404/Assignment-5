
/**
 * Assignment-5: Andersen Pointer Analysis
 * and Indirect Call Graph Update
 */

#include "A5Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
        OptionBase::parseOptions(
            argc, argv,
            "Whole Program Points-to Analysis",
            "[options] <input-bitcode...>"
        );

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);

    consg->dump();

    Andersen andersen(consg);
    auto cg = pag->getCallGraph();

    // Step 1: Compute points-to sets
    andersen.runPointerAnalysis();
    andersen.dumpResult();

    // Step 2: Resolve indirect calls
    andersen.updateCallGraph(cg);

    // Step 3: Output updated call graph
    cg->dump();

    delete consg;

    SVF::LLVMModuleSet::releaseLLVMModuleSet();

    return 0;
}

void Andersen::runPointerAnalysis()
{
    using SVF::NodeID;

    WorkList<NodeID> worklist;
    pts.clear();

    // Initialize Addr constraints
    for (const auto* edge : consg->getAddrCGEdges())
    {
        NodeID object = edge->getSrcID();
        NodeID pointer = edge->getDstID();

        if (pts[pointer].insert(object).second)
            worklist.push(pointer);
    }

    // Andersen fixed-point iteration
    while (!worklist.empty())
    {
        NodeID id = worklist.pop();

        SVF::ConstraintNode* node =
            consg->getConstraintNode(id);

        const std::set<unsigned> pointees = pts[id];

        // Process Load and Store constraints
        for (NodeID object : pointees)
        {
            // Load: q = *p
            for (const auto* load :
                 node->getLoadOutEdges())
            {
                NodeID dst = load->getDstID();

                if (consg->addCopyCGEdge(object, dst))
                    worklist.push(object);
            }

            // Store: *p = q
            for (const auto* store :
                 node->getStoreInEdges())
            {
                NodeID src = store->getSrcID();

                if (consg->addCopyCGEdge(src, object))
                    worklist.push(src);
            }
        }

        // Process Copy constraints
        for (const auto* copy :
             node->getCopyOutEdges())
        {
            NodeID dst = copy->getDstID();

            for (NodeID object : pointees)
            {
                if (pts[dst].insert(object).second)
                    worklist.push(dst);
            }
        }

        // Process GEP constraints
        for (const auto* edge :
             node->getGepOutEdges())
        {
            NodeID dst = edge->getDstID();

            for (NodeID object : pointees)
            {
                NodeID fieldObject = object;

                if (consg->isBlkObjOrConstantObj(object))
                {
                    // Keep special objects unchanged.
                }
                else if (const auto* normal =
                    SVF::SVFUtil::dyn_cast<
                        SVF::NormalGepCGEdge>(edge))
                {
                    fieldObject =
                        consg->getGepObjVar(
                            object,
                            normal->getConstantFieldIdx()
                        );
                }
                else if (SVF::SVFUtil::isa<
                             SVF::VariantGepCGEdge>(edge))
                {
                    fieldObject =
                        consg->getFIObjVar(object);
                }
                else
                {
                    continue;
                }

                if (pts[dst].insert(fieldObject).second)
                    worklist.push(dst);
            }
        }
    }
}

/**
 * Resolve function pointers and update Call Graph.
 */
void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    if (cg == nullptr)
        return;

    SVF::SVFIR* pag = SVF::SVFIR::getPAG();

    const auto& indirectCallsites =
        pag->getIndirectCallsites();

    for (const auto& entry : indirectCallsites)
    {
        const SVF::CallICFGNode* cs = entry.first;
        SVF::NodeID funPtr = entry.second;

        // Obtain points-to set of function pointer
        auto it = pts.find(funPtr);

        if (it == pts.end())
            continue;

        // Examine possible function objects
        for (SVF::NodeID target : it->second)
        {
            const SVF::BaseObjVar* obj =
            pag->getBaseObject(target);

            if (obj == nullptr || !obj->isFunction())
                continue;

            const SVF::FunObjVar* fun =
                SVF::SVFUtil::cast<
                    SVF::FunObjVar>(obj)->getFunction();

            if (fun == nullptr)
                continue;

            const SVF::FunObjVar* callee =
                fun->getDefFunForMultipleModule();

            if (callee == nullptr)
                continue;

            // Check callsite argument compatibility
            if (!SVF::SVFUtil::matchArgs(cs, callee))
                continue;

            // Avoid duplicate indirect call edges
            auto& resolved = cg->getIndCallMap()[cs];

            if (resolved.insert(callee).second)
            {
                cg->addIndirectCallGraphEdge(
                    cs,
                    cs->getCaller(),
                    callee
                );
            }
        }
    }
}
