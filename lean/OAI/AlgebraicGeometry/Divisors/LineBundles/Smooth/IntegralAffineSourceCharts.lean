import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.IntegralOpenSource
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Integral Affine Source Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralAffineSourceCharts.BundleCycles

noncomputable section

/-! Smooth morphisms with geometrically integral fibers admit affine source
and target charts whose restricted projection still has integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

def HasSmoothIntegralAffineSourceCharts {E X : Scheme.{0}} (p : E ⟶ X) : Prop :=
  ∀ z : E, ∃ (U V : Scheme.{0}) (q : V ⟶ U) (i : U ⟶ X) (j : V ⟶ E),
    IsAffine U ∧ IsAffine V ∧ Smooth q ∧ GeometricallyIntegral q ∧
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ z ∈ Set.range j ∧ q ≫ i = j ≫ p

theorem smoothIntegral_hasAffineSourceCharts {E X : Scheme.{0}}
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p] :
    HasSmoothIntegralAffineSourceCharts p := by
  intro z
  obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (p z))
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := p ⁻¹ᵁ U) hzU
  let : IsAffine U := hU
  let : IsAffine V := hV
  have e : V ≤ p ⁻¹ᵁ U := hVU
  let p₀ : V.toScheme ⟶ U.toScheme := p.resLE U V e
  let : Smooth p₀ := inferInstanceAs (Smooth (p.resLE U V e))
  let z₀ : V := ⟨z, hzV⟩
  let W : U.toScheme.Opens := ⟨Set.range p₀, p₀.isOpenMap.isOpen_range⟩
  obtain ⟨r, hr, hzr⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le
    (V := W) ⟨p₀ z₀, ⟨z₀, rfl⟩⟩ (Opens.mem_top _)
  let B : U.toScheme.Opens := U.toScheme.basicOpen r
  let A : V.toScheme.Opens := p₀ ⁻¹ᵁ B
  let : IsAffine B := inferInstanceAs (IsAffine (U.toScheme.basicOpen r))
  have hA : IsAffineOpen A := by
    change IsAffineOpen (p₀ ⁻¹ᵁ U.toScheme.basicOpen r)
    rw [Scheme.preimage_basicOpen_top]
    exact (isAffineOpen_top V.toScheme).basicOpen _
  let : IsAffine A := hA
  let q : A.toScheme ⟶ B.toScheme := p₀ ∣_ B
  let : Smooth q := inferInstanceAs (Smooth (p₀ ∣_ B))
  let i : B.toScheme ⟶ X := B.ι ≫ U.ι
  let j : A.toScheme ⟶ E := A.ι ≫ V.ι
  have hs : q ≫ i = j ≫ p := by
    change (p₀ ∣_ B) ≫ B.ι ≫ U.ι = (A.ι ≫ V.ι) ≫ p
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    change A.ι ≫ p.resLE U V e ≫ U.ι = (A.ι ≫ V.ι) ≫ p
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc]
  let : Surjective q := ⟨by
    intro b
    obtain ⟨a, ha⟩ := hr b.property
    have haB : a ∈ A := by
      change p₀ a ∈ B
      rw [ha]
      exact b.property
    refine ⟨⟨a, haB⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe p₀ B ⟨a, haB⟩).trans ha⟩
  let : GeometricallyIntegral q := Geometric.IntegralOpenSource.BundleCycles.geometricallyIntegral_openSquare p q i j hs
  refine ⟨B.toScheme, A.toScheme, q, i, j, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_, hs⟩
  exact ⟨⟨z₀, hzr⟩, rfl⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralAffineSourceCharts.BundleCycles
