import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

/-! # Kernel Choice Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIso.CM

noncomputable section

/-! Independent finite étale kernel choices are invariant under the actual
PEL-family isomorphism, with every local character and exponent retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N s q : ℕ} [Fact q.Prime]
  {A B : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S} (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A B)
  (χ : Fin s → R →+* ℤ_[q]) (h : ℕ) (a : Fin s → Fin 3 → ℕ)

def comap (F : AbelianScheme.TateComparison.Subgroups.KernelChoices B χ h a) : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ h a := by
  refine ⟨fun v => (F.val v).comapHom e.abelian.hom, fun v => ⟨?_, ?_, ?_⟩⟩
  · exact AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasFiniteEtaleModel_comapIso _ (F.property v).1 e.abelian
  · intro T x hx
    have hb := (F.property v).2.1 T hx
    have he := congrArg (fun J : AbelianScheme.TateComparison.Subgroups.PointSubgroup A.abelian => x ∈ J.atTest T)
      (AbelianScheme.TateComparison.SplitSubgroups.splitBlock_comapIso e (χ v) h)
    exact (iff_of_eq he).mp hb
  · exact AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasGeometricType_comapIso _ (F.property v).2.2 e.abelian

theorem comap_inverse (F : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ h a) :
    comap e χ h a (comap e.symm χ h a F) = F := by
  apply Subtype.ext
  funext v
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro T
  ext x
  change (x ≫ e.abelian.hom) ≫ e.abelian.inv ∈ (F.val v).atTest T ↔
    x ∈ (F.val v).atTest T
  simp only [Category.assoc, e.abelian.hom_inv_id, Category.comp_id]

def equivalence : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ h a ≃ AbelianScheme.TateComparison.Subgroups.KernelChoices B χ h a where
  toFun := comap e.symm χ h a
  invFun := comap e χ h a
  left_inv := comap_inverse e χ h a
  right_inv := comap_inverse e.symm χ h a

theorem equivalence_membership (F : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ h a) (v : Fin s)
    (T : Over S) (x : T ⟶ B.abelian.scheme) :
    x ∈ ((equivalence e χ h a F).val v).atTest T ↔
      x ≫ e.abelian.inv ∈ (F.val v).atTest T := Iff.rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIso.CM
