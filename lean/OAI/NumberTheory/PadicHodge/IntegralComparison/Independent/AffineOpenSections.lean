import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineSections

/-! # Affine Open Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineOpenSections

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {M N : X.Modules}

include hU

theorem surjective [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [hf : Epi f] : Function.Surjective (f.val.app (op U)).hom := by
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let : Epi (F.map f) :=
    @Functor.PreservesEpimorphisms.preserves _ _ _ _ _
      (Functor.preservesEpimorphisms_of_adjunction
        (Scheme.Modules.restrictAdjunction hU.fromSpec)) M N f hf
  have h := (ModuleCat.epi_iff_surjective _).mp
    (AffineSections.gamma_map_epi Γ(X, U) (F.map f))
  change Function.Surjective (f.val.app (op (hU.fromSpec ''ᵁ ⊤))).hom at h
  have hopen : hU.fromSpec ''ᵁ ⊤ = U := by
    apply TopologicalSpace.Opens.ext
    change hU.fromSpec '' Set.univ = (U : Set X)
    rw [Set.image_univ, hU.range_fromSpec]
  rwa [hopen] at h

theorem map_epi [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f) :=
  (ModuleCat.epi_iff_surjective _).mpr (surjective U hU f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineOpenSections
