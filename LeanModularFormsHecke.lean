/-
TEMP(v4.31 bump, 2026-06-14): aggregator target for the Hecke/SMO math surface.

verso-blueprint has no v4.31 release yet, so `blueprint-gen` (the usual driver that
builds the Hecke tree transitively through the Verso `Chapters/`) is disabled during
the bump. This module imports exactly the math modules the Chapters reference, so
`lake build LeanModularFormsHecke` builds the whole Hecke/SMO/eigenform tree on
v4.31 without pulling in Verso. Remove (and restore blueprint-gen) once
verso-blueprint ships v4.31.
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.CoreIdentityProof
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiCrossingCPV
import LeanModularForms.ForMathlib.HW33Clean
import LeanModularForms.ForMathlib.MultipointPV
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.I
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Rho
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.RhoPlusOne
import LeanModularForms.ForMathlib.ValenceFormulaFinal
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Commutativity
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Degree
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Module
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.Degree
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeAction
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.Unified.EigenformFromRing
import LeanModularForms.HeckeRIngs.GL2.Unified.Gamma0RingDn
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.Unified.RingTransport
import LeanModularForms.HeckeRIngs.GL2.Unified.ShimuraHom
import LeanModularForms.HeckeRIngs.GLn.Basic
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.AtkinLehner
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Foundation
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Props
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Surjectivity
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanModularForms.HeckeRIngs.GLn.PolynomialRing
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.SMOObligations.StrongMultiplicityOneFull
