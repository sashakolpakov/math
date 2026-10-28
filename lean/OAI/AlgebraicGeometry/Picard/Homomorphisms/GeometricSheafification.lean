import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Geometric Sheafification -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricSheafification

noncomputable section

/-! An fppf cover of an algebraically closed field has a section.
Consequently sheafification changes no sections at that geometric point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem fppf_sieve_algClosed_eq_top (R : Sieve (Spec (.of k)))
    (hR : R ∈ Scheme.fppfTopology (Spec (.of k))) : R = ⊤ := by
  have : Scheme.fppfPrecoverage.HasIsos := by
    constructor
    intro X Y f hf
    exact f.singleton_mem_fppfPrecoverage
  obtain ⟨Q, hQ, hQR⟩ :=
    Scheme.fppfPrecoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage :=
    inferInstanceAs (Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  obtain ⟨Y, f, hf, y, _⟩ :=
    Scheme.JointlySurjective.exists_eq Q hQ (IsLocalRing.closedPoint k)
  have hi : LocallyOfFinitePresentation f := (hQ.2 hf).2
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  have hne : (Set.univ : Set Y).Nonempty := ⟨y, trivial⟩
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  let a := pointOfClosedPoint f x hx
  have ha : a ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
  apply le_antisymm le_top
  intro Z z _
  have hid : R (𝟙 (Spec (.of k))) := by
    rw [← ha]
    exact R.downward_closed (hQR _ _ hf) a
  simpa only [Category.comp_id] using R.downward_closed hid z

theorem fppf_over_sieve_algClosed_eq_top
    (R : Sieve (Over.mk (𝟙 (Spec (.of k)))))
    (hR : R ∈ (Scheme.fppfTopology.over (Spec (.of k))) (Over.mk (𝟙 _))) : R = ⊤ := by
  apply (Sieve.overEquiv _).injective
  rw [map_top]
  exact fppf_sieve_algClosed_eq_top k _
    ((GrothendieckTopology.mem_over_iff Scheme.fppfTopology R).mp hR)

variable (P : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1))

/-- Every sheafified section over the geometric point comes from a unique original section. -/
theorem toSheafify_algClosed_bijective :
    Function.Bijective ((toSheafify (Scheme.fppfTopology.over (Spec (.of k))) P).app
      (op (Over.mk (𝟙 (Spec (.of k)))))) := by
  let J := Scheme.fppfTopology.over (Spec (.of k))
  let η := toSheafify J P
  constructor
  · intro x y h
    apply (Presheaf.equalizerSieve_eq_top_iff (F := P) x y).mp
    exact fppf_over_sieve_algClosed_eq_top k _ (Presheaf.equalizerSieve_mem J η x y h)
  · intro x
    have hcover := Presheaf.imageSieve_mem J η x
    have htop := fppf_over_sieve_algClosed_eq_top k _ hcover
    have hmem : Presheaf.imageSieve η x (𝟙 (Over.mk (𝟙 (Spec (.of k))))) := by
      rw [htop]
      trivial
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha.trans (by simp)⟩

def geometricSheafificationEquiv :
    P.obj (op (Over.mk (𝟙 (Spec (.of k))))) ≃
      (sheafify (Scheme.fppfTopology.over (Spec (.of k))) P).obj
        (op (Over.mk (𝟙 (Spec (.of k))))) :=
  Equiv.ofBijective _ (toSheafify_algClosed_bijective k P)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricSheafification
