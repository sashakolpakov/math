import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCoefficientSplitting

/-! # Operator Specification -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

section

/-! Native input and output types for the repaired FrobeniusKernel statement.
The source splittings and compact prescription are inputs. Full finite-flat
kernel realization, polarized marked quotients, ordinary targets and their
canonicality are required outputs. No operator identity occurs in a data field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- Every etale line occurs once; equal target points retain multiplicity. -/
def OperatorSpecification.Construction.etaleLineMultiset {q : ℕ} [Fact q.Prime] {X : Type} (f : EtaleSubgroups.Construction.ActiveEtaleLine q → X) : Multiset X := by
  let := Fintype.ofFinite (EtaleSubgroups.Construction.ActiveEtaleLine q)
  exact (Finset.univ : Finset (EtaleSubgroups.Construction.ActiveEtaleLine q)).val.map f

def OperatorSpecification.Construction.nativeGroupIdentityPoint {S : Scheme} (G : Grp (Over S)) (T : Over S) : T ⟶ G.X := 1

def OperatorSpecification.Construction.nativeIsogenyKernelCondition {S : Scheme} {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (T : Over S) (a : T ⟶ A.scheme) : Prop :=
  a ≫ f.hom = 1

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
variable (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))

/-- Actual ordinary group-scheme splittings at every finite level.
The active heights are (1,2); each compact block has heights (3,0) or (0,3). -/
structure Integral.Construction.SplitPELReduction.OrdinaryKernelData where
  compact : D.OrdinaryPoint → Fin s → Bool
  splitting : ∀ (x : D.OrdinaryPoint) (n : ℕ) (v : Fin (s + 1)),
    OrdinaryBlocks.Construction.OrdinaryBlockSplitting (ModuliPoint.Construction.residueClosure q)
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (v, false)) n) q n
      (CMPointsYZQuotients.Construction.l45MultiplicativeHeights (compact x) v) (CMPointsYZQuotients.Construction.l45EtaleHeights (compact x) v)

abbrev Integral.Construction.SplitPELReduction.CompactKernelPrescription := ∀ (x : D.OrdinaryPoint) (n : ℕ) (v : Fin s),
  FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (ModuliPoint.Construction.residueClosure q)
    (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (v.succ, false)) n)

variable (O : D.OrdinaryKernelData j iota' hsplit labels)
variable (C0 : D.CompactKernelPrescription j iota' hsplit labels)

/-- Whole multiplicative compact blocks and the identity subgroup in
etale compact blocks, expressed on all tests rather than an empty scheme. -/
def Integral.Construction.SplitPELReduction.CompactKernelCondition : Prop :=
  ∀ (x : D.OrdinaryPoint) (n : ℕ) (v : Fin s) (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (v.succ, false)) n).X),
    (∃ h : T ⟶ (C0 x n v).group.X, h ≫ (C0 x n v).inclusion.hom.hom = a) ↔
      if O.compact x v then True else a = OperatorSpecification.Construction.nativeGroupIdentityPoint
        (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
          (D.pointDatum x.val).data.action (labels (v.succ, false)) n) T

def Integral.Construction.SplitPELReduction.prescribedXChosen (x : D.OrdinaryPoint) : ∀ v : Fin (s + 1),
    FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (ModuliPoint.Construction.residueClosure q)
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (v, false)) 1) :=
  Fin.cases (FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x 1 0)) (C0 x 1)

def Integral.Construction.SplitPELReduction.prescribedYChosen (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) : ∀ v : Fin (s + 1),
    FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (ModuliPoint.Construction.residueClosure q)
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (v, false)) 1) :=
  Fin.cases (FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (0, false)) (O.splitting x 1 0) L) (C0 x 1)

/-- Z's active source is the literal q-torsion plane; its opposite
annihilator will be computed in q²-torsion by `prescribedFullZKernel`. -/
def Integral.Construction.SplitPELReduction.prescribedZChosen (x : D.OrdinaryPoint) : ∀ v : Fin (s + 1),
    FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (ModuliPoint.Construction.residueClosure q)
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (v, false)) 2) :=
  Fin.cases (FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (0, false)) (O.splitting x 1 0)) (C0 x 2)

abbrev Integral.Construction.SplitPELReduction.prescribedFullXKernel (x : D.OrdinaryPoint) :=
  Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action 1 (s + 1) labels (D.prescribedXChosen j iota' hsplit labels O C0 x)

abbrev Integral.Construction.SplitPELReduction.prescribedFullYKernel (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action 1 (s + 1) labels (D.prescribedYChosen j iota' hsplit labels O C0 x L)

abbrev Integral.Construction.SplitPELReduction.prescribedFullZKernel (x : D.OrdinaryPoint) :=
  Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action 2 (s + 1) labels (D.prescribedZChosen j iota' hsplit labels O C0 x)

theorem Integral.Construction.SplitPELReduction.prescribedZChosen_active_inclusion (x : D.OrdinaryPoint) :
    (D.prescribedZChosen j iota' hsplit labels O C0 x 0).inclusion.hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota' hsplit (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action 2 (labels (0, false)) =
    (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (ModuliPoint.Construction.residueClosure q) q
      (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))).hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota' hsplit (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action 1 (labels (0, false)) :=
  CMPointsAt.Construction.l45ActivePlaneAtLevelTwo_inclusion j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (0, false)) (O.splitting x 1 0)

/-- A full finite-flat realization of the independent kernel, its genuine
polarized O_E-linear marked quotient, and its specified ordinary moduli point.
`QuotientWitness.target` includes the original polarization type, positivity,
Rosati condition and all PEL Lie ranks. -/
structure Integral.Construction.SplitPELReduction.PrescribedOrdinaryQuotient (x : D.OrdinaryPoint) (m : ℕ)
    (kernel : ∀ (T : Over D.integralGeometricBase.left),
      (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop)
    (y : D.OrdinaryPoint) where
  group : Grp (Over D.integralGeometricBase.left)
  inclusion : group.X ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme
  preservesGroup : IsMonHom inclusion
  closed : IsClosedImmersion inclusion.left
  finite : IsFinite group.X.hom
  flat : Flat group.X.hom
  finitePresentation : LocallyOfFinitePresentation group.X.hom
  realizes : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    (∃ h : T ⟶ group.X, h ≫ inclusion = a) ↔ kernel T a
  quotient : D.QuotientWitness (D.pointDatum x.val) m group inclusion
  classifies : D.PointClassifies y.val quotient.target

/-- Uniqueness is equality of full moduli points, allowing different
isomorphic choices of the finite-flat kernel and quotient representatives. -/
def Integral.Construction.SplitPELReduction.CanonicalOrdinaryQuotient (x : D.OrdinaryPoint) (m : ℕ)
    (kernel : ∀ (T : Over D.integralGeometricBase.left),
      (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop)
    (y : D.OrdinaryPoint) : Prop :=
  Nonempty (D.PrescribedOrdinaryQuotient x m kernel y) ∧
    ∀ z : D.OrdinaryPoint, Nonempty (D.PrescribedOrdinaryQuotient x m kernel z) → z = y

/-- The independently defined relative Frobenius kernel on every test
scheme; neither the chosen kernel nor the operator X occurs in this definition. -/
def Integral.Construction.SplitPELReduction.relativeFrobeniusKernelCondition (x : D.OrdinaryPoint)
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) : Prop :=
  OperatorSpecification.Construction.nativeIsogenyKernelCondition (Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))
    (D.pointDatum x.val).data.polarized.abelian) T a

end

/-! Typed underlying inclusions of the literal active line and q-plane
at an ordinary moduli point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
variable (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (O : D.OrdinaryKernelData j iota' hsplit labels) (x : D.OrdinaryPoint)

def Integral.Construction.SplitPELReduction.pointActiveSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q
    (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (0, false)) 1) :=
  ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0)

def Integral.Construction.SplitPELReduction.pointActiveLineInclusion (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (ModuliPoint.Construction.residueClosure q))) q L).X ⟶
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (0, false)) 1).X :=
  (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (ModuliPoint.Construction.residueClosure q) q
    (D.pointActiveSplitting j iota' hsplit labels O x) L).hom.hom

def Integral.Construction.SplitPELReduction.pointActivePlaneInclusion :
    (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of (ModuliPoint.Construction.residueClosure q))) q).X ⟶
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action (labels (0, false)) 2).X :=
  (CMPointsAt.Construction.l45ActivePlaneAtLevelTwo j iota' hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (labels (0, false)) (O.splitting x 1 0)).hom.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
