import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

/-! # Kernel Choice Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceTransport.CM

noncomputable section

/-! Transport actual chosen kernels along a full PEL-family isomorphism.
The same finite subgroup functors and elementary types are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N s q : ℕ} [Fact q.Prime]
  {A B : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S} (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A B)
  (χ : Fin s → R →+* ℤ_[q]) (n : ℕ) (a : Fin s → Fin 3 → ℕ)

def comap (H : AbelianScheme.TateComparison.Subgroups.KernelChoices B χ n a) : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ n a := by
  refine ⟨fun v => (H.val v).comapHom e.abelian.hom, fun v => ⟨?_, ?_, ?_⟩⟩
  · exact AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasFiniteEtaleModel_comapIso _ (H.property v).1 e.abelian
  · intro T x hx
    have hb : x ∈ ((AbelianScheme.TateComparison.Subgroups.splitBlock B (χ v) n).comapHom e.abelian.hom).atTest T :=
      (H.property v).2.1 T hx
    rw [AbelianScheme.TateComparison.SplitSubgroups.splitBlock_comapIso] at hb
    exact hb
  · exact AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasGeometricType_comapIso _ (H.property v).2.2 e.abelian

theorem comap_inverse (H : AbelianScheme.TateComparison.Subgroups.KernelChoices B χ n a) :
    comap e.symm χ n a (comap e χ n a H) = H := by
  apply Subtype.ext
  funext v
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro T
  ext x
  change (x ≫ e.abelian.inv) ≫ e.abelian.hom ∈ (H.val v).atTest T ↔
    x ∈ (H.val v).atTest T
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

def choiceEquiv : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ n a ≃ AbelianScheme.TateComparison.Subgroups.KernelChoices B χ n a where
  toFun := comap e.symm χ n a
  invFun := comap e χ n a
  left_inv H := comap_inverse e.symm χ n a H
  right_inv H := comap_inverse e χ n a H

theorem choiceEquiv_membership (H : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ n a) (v : Fin s)
    (T : Over S) (x : T ⟶ B.abelian.scheme) :
    x ∈ ((choiceEquiv e χ n a H).val v).atTest T ↔
      x ≫ e.abelian.inv ∈ (H.val v).atTest T := Iff.rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceTransport.CM
