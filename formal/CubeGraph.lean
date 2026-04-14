-- CubeGraph: Formal verification of the 3-CUBES framework for 3-SAT
--
-- This library formalizes:
-- 1. Boolean matrices (BoolMat) forming a monoid under ⊗
-- 2. Cubes (variable triplets with gap sets) and CubeGraphs
-- 3. Transfer operators derived from gap compatibility
-- 4. Core theorems: rank-0 → UNSAT, locality, cycle trace semantics

import CubeGraph.BoolMat
import CubeGraph.Basic
import CubeGraph.GapLemmas
import CubeGraph.Theorems
import CubeGraph.PartB
import CubeGraph.ChannelAlignment
import CubeGraph.Topology
import CubeGraph.TreeSAT
import CubeGraph.RankTheory
import CubeGraph.LeafTrimming
import CubeGraph.CNF
import CubeGraph.CycleDP
import CubeGraph.Hierarchy
import CubeGraph.Witness
import CubeGraph.FormulaToGraph
import CubeGraph.HierarchyTheorems
import CubeGraph.GapSheaf
import CubeGraph.Locality
import CubeGraph.CycleIntersection
import CubeGraph.Monodromy
import CubeGraph.GapSheafCech
import CubeGraph.MonodromyCycleOp
import CubeGraph.Holonomy
import CubeGraph.Rank1AC
import CubeGraph.InvertibilityBarrier
import CubeGraph.MUS
import CubeGraph.FiberDichotomy
import CubeGraph.TaylorBarrier
import CubeGraph.TrivialSection
import CubeGraph.HornBarrier
import CubeGraph.DualHornBarrier
import CubeGraph.FunctionalTransfer
import CubeGraph.BarrierSummary
import CubeGraph.MinimalBarrier
import CubeGraph.ZeroDivisors
import CubeGraph.TraceKernel
import CubeGraph.IdempotentRetraction
import CubeGraph.NonCancellative
import CubeGraph.Absorption
import CubeGraph.RowRank
import CubeGraph.Rank1Algebra
import CubeGraph.BandSemigroup
import CubeGraph.Z2Reflection
import CubeGraph.FullSupportComposition
import CubeGraph.NonTransitivity
import CubeGraph.InducedSubgraph
import CubeGraph.MisalignedComposition
import CubeGraph.GeometricReduction
import CubeGraph.Type2Monodromy
import CubeGraph.RankMonotonicity
import CubeGraph.IdempotenceBarrier
import CubeGraph.DimensionThreshold
import CubeGraph.TrivialPolymorphism
import CubeGraph.KConsistency
import CubeGraph.BarringtonConnection
import CubeGraph.Z3Composition
import CubeGraph.Unification
import CubeGraph.BandwidthGap
import CubeGraph.AbstractCSP
import CubeGraph.SchoenebeckAxiom
import CubeGraph.SchoenebeckChain
import CubeGraph.BarrierTheorem
import CubeGraph.InformationChannel
import CubeGraph.IntegerMonodromy
import CubeGraph.Rank1Protocol
import CubeGraph.QuantitativeGap
import CubeGraph.QueryLowerBound
import CubeGraph.CSPDecomposition
import CubeGraph.LiftingTheorem
import CubeGraph.KWGame
import CubeGraph.MonotoneSizeLB
import CubeGraph.Rank1Bubbles
import CubeGraph.Resolution
import CubeGraph.IdempotentSemiring
import CubeGraph.RankWidthTransfer
import CubeGraph.SublinearER
import CubeGraph.SpreadingCompression
import CubeGraph.BorromeanAC0
import CubeGraph.InformationBottleneckComplete
import CubeGraph.FixedPointGap
import CubeGraph.SymmetryBreaking
import CubeGraph.ERAuxiliaryBlind
import CubeGraph.ERStructural
import CubeGraph.BorromeanFullGraph
import CubeGraph.ERExtendable
import CubeGraph.ERBorromeanFull
import CubeGraph.ERKConsistentBridge
import CubeGraph.ERAggregateBricks
import CubeGraph.ERKConsistentProof
import CubeGraph.ERKConsistentInduction
import CubeGraph.ERKConsistent6Gap
import CubeGraph.ABDWidthLowerBound
import CubeGraph.BSWWidthSize
import CubeGraph.ERLowerBound
import CubeGraph.PCLowerBound
import CubeGraph.CPLowerBound
import CubeGraph.AC0FregeLowerBound
import CubeGraph.EFLowerBound
import CubeGraph.DepthFregeLowerBound
import CubeGraph.FregeLowerBound
import CubeGraph.PolynomialReduction
import CubeGraph.BinomComplete
import CubeGraph.NoCancellation
import CubeGraph.GapPreservingSubgroup
import CubeGraph.StellaOctangula
-- Sigma4SevenSteps not imported here due to pre-existing name collision
-- (Sigma3Irrationality.honest_gap vs InformationBottleneckComplete.honest_gap).
-- Build individually: `lake build CubeGraph.Sigma4SevenSteps`
import CubeGraph.TransferMonoid
import CubeGraph.T3StarNoGroup
import CubeGraph.T3StarACC0
import CubeGraph.FregeStructure
import CubeGraph.NonAffine
import CubeGraph.PolymorphismBarrier
import CubeGraph.StarMatrix
import CubeGraph.CubeSymmetriesGroup
import CubeGraph.ComputationalNoether
import CubeGraph.MonotoneAxioms
import CubeGraph.BooleanEncoding
import CubeGraph.MonotoneLowerBound
import CubeGraph.BoundedDepthFregeBarrier
import CubeGraph.CutReuse
import CubeGraph.DistinctCompositions
import CubeGraph.WidthReuse
import CubeGraph.MonotoneProofConversion
import CubeGraph.MPCResolution
import CubeGraph.GadgetNOR
import CubeGraph.SufficientLemma
import CubeGraph.InterpolantMonotone
import CubeGraph.CPLowerBoundMFI
import CubeGraph.InterpolantCircuitLB
import CubeGraph.SemanticBridge
import CubeGraph.EraseOnlyCollapse
import CubeGraph.GapPath
import CubeGraph.FiberSize
import CubeGraph.MPLossy
import CubeGraph.MonotoneDepthLB
import CubeGraph.ContextExplosion
import CubeGraph.ExtensionExplosion
import CubeGraph.LabelErasure
import CubeGraph.AnonymousBranching
import CubeGraph.InfoIrrecoverable
import CubeGraph.HierarchyExtended
import CubeGraph.FullColSup
import CubeGraph.GapSummary
import CubeGraph.TheoremX
import CubeGraph.TreeLikeFrege
import CubeGraph.ProofComplexityModel
import CubeGraph.ConditionalMFI
-- FregeDepthCollapse not imported here due to name collision
-- (ConditionalMFI.minFregeSize vs FregeLowerBound.minFregeSize).
-- Build individually: `lake build CubeGraph.FregeDepthCollapse`
import CubeGraph.RankOrAnd
-- AugmentationBarrier not imported here due to name collision
-- (ResolutionFramework.minResWidth vs ABDWidthLowerBound.minResWidth).
-- Build individually: `lake build CubeGraph.AugmentationBarrier`
