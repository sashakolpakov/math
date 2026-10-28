import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedHomDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientFactor
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi

/-! # Recovered Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredDescent.Construction

noncomputable section

/-! Descent of a specified homomorphism through actual source and
target recoveries. Finite etale isogenies retain their geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) (D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (eA : C.scheme ≅ (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).scheme)
    (eB : D.scheme ≅ (B.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).scheme)
    [IsMonHom eA.hom] [IsMonHom eB.hom]

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_hom_of_recovery (f : C.scheme ⟶ D.scheme) [IsMonHom f] :
    ∃ w : A.scheme ⟶ B.scheme, IsMonHom w ∧
      eA.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map w =
        f ≫ eB.hom := by
  let f' := eA.inv ≫ f ≫ eB.hom
  have : IsMonHom f' := inferInstance
  obtain ⟨w, hw, he⟩ := AlgebraicallyClosedHomDescent.Construction.algebraicallyClosed_field_hom_descends k K A B f'
  refine ⟨w, hw, ?_⟩
  rw [he]
  exact eA.hom_inv_id_assoc (f ≫ eB.hom)

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_etale_isogeny_of_recovery
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny C D) [Etale f.hom.left] :
    ∃ w : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B, Etale w.hom.left ∧
      eA.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map w.hom =
        f.hom ≫ eB.hom := by
  let u := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback u
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  obtain ⟨w, hw, he⟩ := algebraicallyClosed_hom_of_recovery k K A B C D eA eB f.hom
  have : IsMonHom w := hw
  have hc : F.map w = eA.inv ≫ f.hom ≫ eB.hom := by
    rw [← he, eA.inv_hom_id_assoc]
  have : IsIso eA.inv.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map eA.inv))
  have : IsIso eB.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map eB.hom))
  have het : Etale (F.map w).left := by rw [hc]; change Etale (eA.inv.left ≫ f.hom.left ≫ eB.hom.left); infer_instance
  have hsurj : Surjective (F.map w).left := by
    rw [hc]
    change Surjective (eA.inv.left ≫ f.hom.left ≫ eB.hom.left)
    infer_instance
  have : Etale w.left := PELModuli.IntegralModel.Arithmetic.QuotientFactor.property_of_fpqc_baseChange u (@Etale) w het
  have : Surjective w.left := PELModuli.IntegralModel.Arithmetic.QuotientFactor.property_of_fpqc_baseChange u (@Surjective) w hsurj
  have : IsProper (w.left ≫ B.scheme.hom) := w.w.symm ▸ inferInstanceAs (IsProper A.scheme.hom)
  have : IsProper w.left := IsProper.of_comp w.left B.scheme.hom
  have : IsFinite w.left := TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified w.left
  exact ⟨⟨w, hw, inferInstance, inferInstance, inferInstance⟩, inferInstance, he⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredDescent.Construction
