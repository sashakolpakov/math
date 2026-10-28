import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultilinearRestriction

/-! # Tensor Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor

noncomputable section

/-! The universal tensor-power property is preserved by restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L P : Y.Modules} {n : ℕ}

/-- An isomorphic representing sheaf has the same universal tensor-power property. -/
theorem Powers.IsTensorPower.of_targetIso {Q : Y.Modules} (hP : Powers.IsTensorPower L n P) (e : P ≅ Q) :
    Powers.IsTensorPower L n Q := by
  obtain ⟨β, hβ⟩ := hP
  refine ⟨β.postcomp e.hom, fun R => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply (cancel_epi e.hom).mp
    apply (hβ R).injective
    exact (β.postcomp_comp e.hom a).trans
      (hab.trans (β.postcomp_comp e.hom b).symm)
  · intro γ
    obtain ⟨a, ha⟩ := (hβ R).surjective γ
    refine ⟨e.inv ≫ a, ?_⟩
    exact (β.postcomp_comp e.hom (e.inv ≫ a)).symm.trans
      ((congrArg (fun h => β.postcomp h) (e.hom_inv_id_assoc a)).trans ha)

/-- A tensor power of a module sheaf restricts to the tensor power on an open subscheme. -/
theorem Powers.IsTensorPower.restrict (hP : Powers.IsTensorPower L n P) (f : X ⟶ Y) [IsOpenImmersion f] :
    Powers.IsTensorPower (L.restrict f) n (P.restrict f) := by
  obtain ⟨β, hβ⟩ := hP
  refine ⟨β.restrict f, fun Q => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply ((Scheme.Modules.restrictAdjunction f).homEquiv P Q).injective
    apply (hβ ((Scheme.Modules.pushforward f).obj Q)).injective
    exact (β.restrictHomEquiv_postcomp f a).symm.trans
      ((congrArg (Powers.SheafMultilinearMap.restrictHomEquiv f L n Q) hab).trans
        (β.restrictHomEquiv_postcomp f b))
  · intro γ
    obtain ⟨a, ha⟩ := (hβ ((Scheme.Modules.pushforward f).obj Q)).surjective
      (Powers.SheafMultilinearMap.restrictHomEquiv f L n Q γ)
    let b := ((Scheme.Modules.restrictAdjunction f).homEquiv P Q).symm a
    refine ⟨b, (Powers.SheafMultilinearMap.restrictHomEquiv f L n Q).injective ?_⟩
    exact (β.restrictHomEquiv_postcomp f b).trans
      ((congrArg (fun h => β.postcomp h)
        (((Scheme.Modules.restrictAdjunction f).homEquiv P Q).apply_symm_apply a)).trans ha)

/-- The canonical module-sheaf pullback along an open immersion preserves tensor powers. -/
theorem Powers.IsTensorPower.pullback_of_isOpenImmersion (hP : Powers.IsTensorPower L n P)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    Powers.IsTensorPower ((Scheme.Modules.pullback f).obj L) n ((Scheme.Modules.pullback f).obj P) :=
  ((hP.restrict f).of_sourceIso ((Scheme.Modules.restrictFunctorIsoPullback f).app L)).of_targetIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor
