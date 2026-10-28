import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ConstantSubgroups
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantGroupBaseChange

/-! # Etale Subgroup Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleSubgroupDescent

noncomputable section

/-! Effective arithmetic models of actual complex finite étale subgroups.
The finite label group, the arithmetic closed embedding, the cartesian
comparison, and the equality with the original subgroup map are constructed.
No descended subgroup model or descent datum is supplied as an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (H : Over (Spec (.of K))) [GrpObj H] [IsFinite H.hom] [Etale H.hom]
  (Q : Over (Spec (.of ℂ))) [GrpObj Q] [IsFinite Q.hom] [Etale Q.hom]

/-- A complex finite étale subgroup of an arithmetic finite étale group
scheme has an actual closed model over a constructed finite extension. -/
theorem finite_etale_subgroup_descends
    (i : Q ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj H)
    [IsMonHom i] [Mono i] (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ), B.denominator = N ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G),
        ∃ (j : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G ⟶
            (Over.pullback B.fieldExtension).obj H)
          (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of ℂ)) G ≅ Q)
          (q : Q.left ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).left),
          IsMonHom j ∧ IsClosedImmersion j.left ∧ IsMonHom e.hom ∧
            IsFinite (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ∧
            Etale (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ∧
            IsPullback q Q.hom (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom
              (Spec.map (CommRingCat.ofHom B.embedding)) ∧
            q ≫ j.left ≫ pullback.fst H.hom B.fieldExtension =
              i.left ≫ pullback.fst H.hom (Spec.map (CommRingCat.ofHom κ)) ∧
            ∃ γ : Q ≅ (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj
                (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G),
              IsMonHom γ.hom ∧ γ.hom.left ≫
                pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom
                  (Spec.map (CommRingCat.ofHom B.embedding)) = q := by
  obtain ⟨G, hG, hfin, e, he⟩ := ConstantBaseChange.ConstantGroupModels.exists_constant_group_model Q
  let := he
  let u := e.hom ≫ i
  have : IsMonHom u := inferInstanceAs (IsMonHom (e.hom ≫ i))
  have : Mono u := inferInstanceAs (Mono (e.hom ≫ i))
  let aC : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of ℂ)) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj H) :=
    (IsMonHom.monoidHom u (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of ℂ)))).comp
      (ConstantBaseChange.ConstantGroupModels.labels (Spec (.of ℂ)) G)
  let E := FieldGroupPoints.fieldGroupPointsMulEquiv (Spec.map (CommRingCat.ofHom κ)) H
  let a := E.toMonoidHom.comp aC
  have ha : Function.Injective a := by
    intro x y hxy
    apply ConstantBaseChange.ConstantGroupModels.labels_injective (Spec (.of ℂ)) G
    apply (cancel_mono u).mp
    exact E.injective hxy
  obtain ⟨B, j, hBN, hjgroup, hjclosed, hfinite, hetale, hcoords⟩ :=
    Arithmetic.ConstantSubgroups.arithmetic_closed_constant_subgroup κ H G a ha N hN
  let ψ := Spec.map (CommRingCat.ofHom B.embedding)
  let q : Q.left ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).left :=
    e.inv.left ≫ ConstantBaseChange.ConstantGroupModels.scalarMap ψ G
  let eQ : Q.left ≅ pullback (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ψ :=
    ((Over.forget (Spec (.of ℂ))).mapIso e.symm) ≪≫
      ((Over.forget (Spec (.of ℂ))).mapIso (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso ψ G))
  have hqfst : eQ.hom ≫ pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ψ = q := by
    change (e.inv.left ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso ψ G).hom.left) ≫ _ = _
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f => e.inv.left ≫ f) (ConstantBaseChange.ConstantGroupModels.baseChangeIso_fst ψ G))
  have hqsnd : eQ.hom ≫ pullback.snd (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ψ = Q.hom := by
    change (e.inv.left ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso ψ G).hom.left) ≫ _ = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => e.inv.left ≫ f) (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso ψ G).hom.w).trans e.inv.w)
  have hqb : q ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom = Q.hom ≫ ψ := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => e.inv.left ≫ f) (ConstantBaseChange.ConstantGroupModels.scalarMap_base ψ G)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ ψ) e.inv.w)))
  have hcart : IsPullback q Q.hom (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ψ :=
    IsPullback.of_iso_pullback ⟨hqb⟩ eQ hqfst hqsnd
  have hmap : q ≫ j.left ≫ pullback.fst H.hom B.fieldExtension =
      i.left ≫ pullback.fst H.hom (Spec.map (CommRingCat.ofHom κ)) := by
    let eR : (∐ fun _ : G => Spec (.of ℂ)) ≅ Q.left := (Over.forget (Spec (.of ℂ))).mapIso e
    let jR : (∐ fun _ : G => Spec (.of B.extension.carrier)) ⟶ pullback H.hom B.fieldExtension := j.left
    let iR : Q.left ⟶ pullback H.hom (Spec.map (CommRingCat.ofHom κ)) := i.left
    apply (cancel_epi eR.hom).mp
    change eR.hom ≫ (eR.inv ≫ ConstantBaseChange.ConstantGroupModels.scalarMap ψ G) ≫
      jR ≫ pullback.fst H.hom B.fieldExtension =
        eR.hom ≫ iR ≫ pullback.fst H.hom (Spec.map (CommRingCat.ofHom κ))
    simp only [Category.assoc, eR.hom_inv_id_assoc]
    apply Sigma.hom_ext
    intro g
    rw [ConstantBaseChange.ConstantGroupModels.component_scalarMap_assoc]
    have hc := hcoords g
    change ψ ≫ (Sigma.ι (fun _ : G => Spec (.of B.extension.carrier)) g ≫ jR) ≫
      pullback.fst H.hom B.fieldExtension = (a g).left at hc
    have ha' : (a g).left =
        Sigma.ι (fun _ : G => Spec (.of ℂ)) g ≫ eR.hom ≫ iR ≫
          pullback.fst H.hom (Spec.map (CommRingCat.ofHom κ)) := by
      have h := FieldGroupPoints.fieldGroupPointsMulEquiv_left (Spec.map (CommRingCat.ofHom κ)) H (aC g)
      change (a g).left = _ at h
      have hAC : aC g = AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component (Spec (.of ℂ)) g ≫ u :=
        congrArg (fun p => p ≫ u) (ConstantBaseChange.ConstantGroupModels.labels_eq_component (Spec (.of ℂ)) G g)
      exact h.trans ((congrArg (fun p => p.left ≫
        pullback.fst H.hom (Spec.map (CommRingCat.ofHom κ))) hAC).trans
          (by simp only [u, Over.comp_left, Category.assoc]; rfl))
    simpa only [Category.assoc] using hc.trans ha'
  let γ := e.symm ≪≫ AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso ψ G
  have hγ : IsMonHom γ.hom := by
    change IsMonHom (e.inv ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso ψ G).hom)
    infer_instance
  exact ⟨B, hBN, G, hG, hfin, j, e, q, hjgroup, hjclosed, he,
    hfinite, hetale, hcart, hmap, γ, hγ, hqfst⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleSubgroupDescent
