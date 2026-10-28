import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualCochain
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.ComplexExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport

/-! # Dual Field Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualFieldSupport

noncomputable section

/-! Finite duality and scalar extension preserve the field support condition for a complex concentrated in a finite interval. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

def dualCochainBaseChangeIso (B : Type u) [CommRing B] [Algebra R B]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q)) :
    ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.down ℕ)).obj
        (HilbertConstruction.Module.DualFunctor.dualModuleComplex C) ≅
      HilbertConstruction.Module.DualFunctor.dualModuleComplex
        (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => ?_) ?_
  · have : Module.Finite R (C.X q) := hfin q
    have : Module.Free R (C.X q) := hfree q
    exact (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv (R := R) B (C.X q)).toModuleIso
  · intro i j _
    have : Module.Finite R (C.X i) := hfin i
    have : Module.Free R (C.X i) := hfree i
    have : Module.Finite R (C.X j) := hfin j
    have : Module.Free R (C.X j) := hfree j
    exact ModuleCat.hom_ext (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv_naturality (R := R) B (C.d j i).hom).symm

theorem boundedDualCochain_fieldSupport
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q)) (I : Ideal R)
    (hfield : Cochain.FieldSupport.CochainFieldSupport C I) : Cochain.FieldSupport.CochainFieldSupport (DualCochain.boundedDualCochain C g) I := by
  intro B _ _ hnot
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  let CB := (F.mapHomologicalComplex (.up ℕ)).obj C
  let KB := (F.mapHomologicalComplex (.down ℕ)).obj (HilbertConstruction.Module.DualFunctor.dualModuleComplex C)
  have hCB : CB.Acyclic := by
    intro q
    exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C q).mpr (hfield B hnot q)
  have hKB : KB.Acyclic := by
    intro q
    let e := dualCochainBaseChangeIso B C hfin hfree
    have hz : IsZero ((HilbertConstruction.Module.DualFunctor.dualModuleComplex CB).homology q) :=
      ((HilbertConstruction.Module.DualFunctor.dualModuleComplex CB).exactAt_iff_isZero_homology q).mp
        (HilbertConstruction.Module.DualFunctor.field_dualModuleComplex_acyclic CB hCB q)
    exact (KB.exactAt_iff_isZero_homology q).mpr
      (IsZero.of_iso hz (HomologicalComplex.homologyMapIso e q))
  let : KB.IsStrictlySupported (DualCochain.finiteDualEmbedding g) := {
    isZero := fun q hq => by
      have hz := hbound q ((DualCochain.finiteDualEmbedding_outside_iff g q).mp hq)
      have : Subsingleton (C.X q) := ModuleCat.subsingleton_of_isZero hz
      change IsZero (ModuleCat.of B (B ⊗[R] Module.Dual R (C.X q)))
      exact ModuleCat.isZero_of_subsingleton _ }
  have hrestrict : ((F.mapHomologicalComplex (HilbertConstruction.Finite.CochainTruncation.finiteCochainShape g)).obj
      (DualCochain.finiteDualCochain C g)).Acyclic := by
    change (KB.restriction (DualCochain.finiteDualEmbedding g)).Acyclic
    exact Additive.ComplexExtension.supported_restriction_acyclic (DualCochain.finiteDualEmbedding g) KB hKB
  have hdualB : ((F.mapHomologicalComplex (.up ℕ)).obj (DualCochain.boundedDualCochain C g)).Acyclic :=
    Additive.ComplexExtension.additive_extend_acyclic F (DualCochain.finiteDualCochain C g) (HilbertConstruction.Finite.CochainTruncation.finiteCochainEmbedding g) hrestrict
  intro q
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor (DualCochain.boundedDualCochain C g) q).mp (hdualB q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DualFieldSupport
