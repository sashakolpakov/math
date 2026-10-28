import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechComplex

/-! # Cech Zero Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechZeroCycles.Construction

noncomputable section

/-! Actual global sections at each infinitesimal level are the reduced native Cech zero-cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

include hcover in
omit [X.IsSeparated] [LinearOrder ι] [Finite ι] in
theorem infinitesimalCechCover_covers (n : ℕ) :
    iSup (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) = ⊤ := by
  apply top_unique
  intro x _
  have hx : pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) x ∈ iSup U := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The actual structure sections on X_n are exactly the zero-cycles of the reduced Cech complex. -/
def infinitesimalSectionsZeroCyclesEquiv (n : ℕ) :
    (RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).obj (op ⊤) ≃ₗ[R]
      ((AdicReduction.Construction.adicReductionComplex (I ^ (n + 1)) (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U)).d 0 1).hom.ker :=
  (RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
    (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i)
      (infinitesimalCechCover_covers I f U hcover n)).trans
    (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (CechComplex.Construction.infinitesimalCechComplexIso I f U hU n).inv)

theorem infinitesimalSectionsZeroCyclesEquiv_value (n : ℕ)
    (s : (RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).obj (op ⊤)) :
    (CechTerms.Construction.infinitesimalCechTermIso I f U hU n 0).hom
        (infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n s).val =
      (RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
        (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i)
          (infinitesimalCechCover_covers I f U hcover n) s).val := by
  rw [infinitesimalSectionsZeroCyclesEquiv, LinearEquiv.trans_apply,
    Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
  change (CechTerms.Construction.infinitesimalCechTermIso I f U hU n 0).hom
    ((CechTerms.Construction.infinitesimalCechTermIso I f U hU n 0).inv _) = _
  exact ConcreteCategory.congr_hom (CechTerms.Construction.infinitesimalCechTermIso I f U hU n 0).inv_hom_id _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechZeroCycles.Construction
