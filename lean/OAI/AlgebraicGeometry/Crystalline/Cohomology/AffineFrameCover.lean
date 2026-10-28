import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothFrames
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Affine Frame Cover -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover

noncomputable section

/-!
# A fixed smooth frame covers the affine crystalline site

For an affine residual scheme and a smooth affine lift, every object of
the native crystalline site maps to some p-power level of the fixed
frame. These maps form a presheaf of nonempty sets. This is the
presentation presheaf used in the crystalline Čech construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]

abbrev affineScheme : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))

variable (Q : Site.Object p k (affineScheme k B))

/-- The algebra map corresponding to the actual affine-open immersion. -/
def residualMap : B →ₐ[k] Q.residueRing where
  __ := (Spec.preimage Q.immersion).hom
  commutes' c := by
    have he : CommRingCat.ofHom (algebraMap k B) ≫ Spec.preimage Q.immersion =
        CommRingCat.ofHom (algebraMap k Q.residueRing) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact Q.over_base
    exact ConcreteCategory.congr_hom he c

theorem residualMap_spec : Spec.map (CommRingCat.ofHom (residualMap p k B Q).toRingHom) =
    Q.immersion := Spec.map_preimage Q.immersion

variable (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

/-- The fixed frame level in the native crystalline site of Spec B. -/
def frame (n : ℕ) : Site.Object p k (affineScheme k B) :=
  SmoothFrames.SmoothCrystallineFrames.siteFrame p k B A r hbase hr (affineScheme k B)
    (𝟙 _) (Category.id_comp _) n

include hr hbase in
theorem exists_frameMap [Algebra.Smooth (WittVector p k) A] :
    ∃ n : ℕ, Nonempty (Q ⟶ frame p k B A r hr hbase n) := by
  obtain ⟨n, g, _⟩ := SmoothFrames.SmoothCrystallineFrames.exists_siteFrameMorphism p k B A r hbase hr
    (affineScheme k B) (𝟙 _) (Category.id_comp _) Q (residualMap p k B Q)
    ((Category.comp_id _).trans (residualMap_spec p k B Q))
  exact ⟨n, ⟨g⟩⟩

/-- Choices of a frame level and a map into it, varying contravariantly in the object. -/
def presentations : (Site.Object p k (affineScheme k B))ᵒᵖ ⥤ Type u where
  obj T := Σ n : ℕ, T.unop ⟶ frame p k B A r hr hbase n
  map a := ↾fun z => ⟨z.1, a.unop ≫ z.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Sigma.ext rfl (heq_of_eq (Category.id_comp z.2))
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Sigma.ext rfl (heq_of_eq (Category.assoc b.unop a.unop z.2))

instance presentations_nonempty [Algebra.Smooth (WittVector p k) A]
    (T : (Site.Object p k (affineScheme k B))ᵒᵖ) :
    Nonempty ((presentations p k B A r hr hbase).obj T) := by
  obtain ⟨n, ⟨g⟩⟩ := exists_frameMap p k B T.unop A r hr hbase
  exact ⟨⟨n, g⟩⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover
