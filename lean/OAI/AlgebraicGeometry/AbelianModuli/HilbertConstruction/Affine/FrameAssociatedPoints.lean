import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Frame Associated Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FrameAssociatedPoints

noncomputable section

/-! A framed line bundle acting on an affine coherent sheaf has a finite family of actual scheme points whose simultaneous nonvanishing guarantees injective multiplication. The points come from the associated primes of the actual affine section module. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} [IsAffine X]

theorem affine_basicOpen_isoSpec_inv_mem
    (P : PrimeSpectrum Γ(X, ⊤)) (r : Γ(X, ⊤)) :
    X.isoSpec.inv P ∈ X.basicOpen r ↔ r ∉ P.asIdeal := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen X r]
  change X.toSpecΓ (X.isoSpec.inv P) ∈ PrimeSpectrum.basicOpen r ↔ _
  have he : X.toSpecΓ (X.isoSpec.inv P) = P :=
    congrArg (fun f : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) => f P) X.isoSpec.inv_hom_id
  rw [he]
  rfl

theorem affine_sectionNonvanishing_isoSpec_inv_mem
    (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    (e : L.sheaf ≅ Line.Bundles.structureModule X) (P : PrimeSpectrum Γ(X, ⊤)) :
    X.isoSpec.inv P ∈ Ample.LineBundles.sectionNonvanishing s ↔
      Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom) ∉ P.asIdeal := by
  have he : Ample.LineBundles.sectionNonvanishing s = X.basicOpen (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) :=
    (Ample.Powers.sectionNonvanishing_comp_iso s e).symm.trans (Scalar.Nonvanishing.sectionNonvanishing_scalar (s ≫ e.hom))
  rw [he, affine_basicOpen_isoSpec_inv_mem]

theorem moduleSectionMultiply_mono_of_associatedPoint_nonvanishing
    [IsNoetherianRing Γ(X, ⊤)] (L : Line.Bundles.LineBundle X) (M : X.Modules) [M.IsQuasicoherent]
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X)
    (hs : ∀ P : associatedPrimes Γ(X, ⊤) Γ(M, ⊤),
      X.isoSpec.inv (show PrimeSpectrum Γ(X, ⊤) from ⟨P.val, P.property.isPrime⟩) ∈
        Ample.LineBundles.sectionNonvanishing s) : Mono (HilbertConstruction.Module.SectionMultiplication.moduleSectionMultiply L M s) := by
  apply (HilbertConstruction.Module.SectionMultiplication.moduleSectionMultiply_mono_iff_avoids_associatedPrimes L M s e).mpr
  intro P hP
  exact (affine_sectionNonvanishing_isoSpec_inv_mem L s e ⟨P, hP.isPrime⟩).mp (hs ⟨P, hP⟩)

theorem affine_exists_finite_section_regular_test
    [IsNoetherianRing Γ(X, ⊤)] (L : Line.Bundles.LineBundle X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (e : L.sheaf ≅ Line.Bundles.structureModule X) :
    ∃ (ι : Type u) (_ : Finite ι) (x : ι → X),
      ∀ s : Line.Bundles.structureModule X ⟶ L.sheaf,
        (∀ i, x i ∈ Ample.LineBundles.sectionNonvanishing s) → Mono (HilbertConstruction.Module.SectionMultiplication.moduleSectionMultiply L M s) := by
  have : Module.Finite Γ(X, ⊤) Γ(M, ⊤) := QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite M
  let ι := associatedPrimes Γ(X, ⊤) Γ(M, ⊤)
  have : Finite ι := (associatedPrimes.finite Γ(X, ⊤) Γ(M, ⊤)).to_subtype
  let x : ι → X := fun P => X.isoSpec.inv
    (show PrimeSpectrum Γ(X, ⊤) from ⟨P.val, P.property.isPrime⟩)
  exact ⟨ι, inferInstance, x,
    fun s hs => moduleSectionMultiply_mono_of_associatedPoint_nonvanishing L M s e hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FrameAssociatedPoints
