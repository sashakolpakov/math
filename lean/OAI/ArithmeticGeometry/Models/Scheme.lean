import OAI.ArithmeticGeometry.Models.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Scheme -/

namespace OAI.ArithmeticGeometry.Models.Scheme.Constructions.Foundations

/-! Scheme-theoretic foundations for Foundations, independent of graph statement stubs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField TensorProduct

universe u

abbrev FinitePresentationMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

/-- Equal base maps give canonically isomorphic base changes, independently
of the chosen pullbacks. -/
noncomputable def baseChangeCongr {S T : Scheme.{u}} {f g : T ⟶ S}
    [HasPullbacksAlong f] [HasPullbacksAlong g] (h : f = g) (X : Over S) :
    (Over.pullback f).obj X ≅ (Over.pullback g).obj X := by
  subst g
  exact Iso.refl _

/-- The affine scheme over its coefficient ring. -/
noncomputable abbrev affineOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

theorem affineOver_finitePresentation
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    FinitePresentationMorphism (affineOver R A).hom := by
  change FinitePresentationMorphism (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  refine ⟨?_, inferInstance, inferInstance⟩
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The affine tensor-product description respects the map to the new base. -/
noncomputable def baseChangeAffineIso
    (R K A : Type u) [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (affineOver R A) ≅ affineOver K (K ⊗[R] A) :=
  Over.isoMk
    (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R K A)
    (by
      change (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R K A).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))) = _
      rw [pullbackSpecIso_hom_fst, pullbackSymmetry_hom_comp_fst]
      rfl)

/-- An algebra isomorphism gives an isomorphism over the coefficient scheme. -/
noncomputable def affineOverIso
    {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    affineOver K A ≅ affineOver K B :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op)
    (by
      change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) =
          Spec.map (CommRingCat.ofHom (algebraMap K A))
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact e.symm.commutes x)

/-- The integral affine model recovers the original affine scheme over `K`. -/
theorem affine_scheme_has_integral_model
    (K A : Type u) [Field K] [NumberField K] [CommRing A] [Algebra K A]
    [Algebra.FinitePresentation K A] (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      ∃ X₀ : Over (Spec (CommRingCat.of (Localization.Away (N : 𝓞 K)))),
        FinitePresentationMorphism X₀.hom ∧
        Nonempty ((Over.pullback
          (Spec.map (CommRingCat.ofHom (Models.Algebra.Constructions.Foundations.integersAwayToField K N hN)))).obj X₀ ≅
            affineOver K A) := by
  obtain ⟨N, hN, hd, A₀, hR, hA, hFP, ⟨e⟩⟩ :=
    Models.Algebra.Constructions.Foundations.finitely_presented_algebra_has_integral_model K A N₀ hN₀
  let L := Localization.Away (N : 𝓞 K)
  let : Algebra L K := (Models.Algebra.Constructions.Foundations.integersAwayToField K N hN).toAlgebra
  let : CommRing A₀ := hR
  let : Algebra L A₀ := hA
  let : Algebra.FinitePresentation L A₀ := hFP
  exact ⟨N, hN, hd, affineOver L A₀, affineOver_finitePresentation L A₀,
    ⟨baseChangeAffineIso L K A₀ ≪≫ affineOverIso e⟩⟩

end OAI.ArithmeticGeometry.Models.Scheme.Constructions.Foundations
