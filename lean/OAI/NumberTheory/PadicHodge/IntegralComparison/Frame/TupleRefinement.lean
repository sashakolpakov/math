import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionFaceMaps

/-! # Tuple Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement

noncomputable section

/-! A genuine map of frame families induces maps of their nonempty tuple
products, compatible with every tuple face and degeneracy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D] (T : C ⥤ D)
  {ι κ : Type v} (F : ι → C) (G : κ → D) (ρ : ι → κ)
  (α : ∀ i, T.obj (F i) ⟶ G (ρ i))

def map (a : ℕ) (t : Fin (a + 1) → ι) :
    T.obj (Presentation.TupleProducts.family F a t) ⟶
      Presentation.TupleProducts.family G a (ρ ∘ t) :=
  Pi.lift (fun b => T.map (Pi.π (fun c => F (t c)) b) ≫ α (t b))

theorem projection (a : ℕ) (t : Fin (a + 1) → ι) (b : Fin (a + 1)) :
    TupleRefinement.map T F G ρ α a t ≫ Pi.π (fun c => G (ρ (t c))) b =
      T.map (Pi.π (fun c => F (t c)) b) ≫ α (t b) := Pi.lift_comp_π _ b

theorem naturality (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι) :
    T.map (Presentation.ResolutionFaceMaps.productMap F θ t) ≫ TupleRefinement.map T F G ρ α b (t ∘ θ) =
      TupleRefinement.map T F G ρ α a t ≫ Presentation.ResolutionFaceMaps.productMap G θ (ρ ∘ t) := by
  apply Pi.hom_ext
  intro j
  have hF : Presentation.ResolutionFaceMaps.productMap F θ t ≫
      Pi.π (fun c => F ((t ∘ θ) c)) j = Pi.π (fun c => F (t c)) (θ j) := Pi.lift_comp_π _ j
  have hG : Presentation.ResolutionFaceMaps.productMap G θ (ρ ∘ t) ≫
      Pi.π (fun c => G (ρ ((t ∘ θ) c))) j = Pi.π (fun c => G (ρ (t c))) (θ j) := Pi.lift_comp_π _ j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => T.map (Presentation.ResolutionFaceMaps.productMap F θ t) ≫ z)
      (projection T F G ρ α b (t ∘ θ) j)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ α (t (θ j)))
          ((T.map_comp _ _).symm.trans (congrArg T.map hF))).trans
          ((projection T F G ρ α a t (θ j)).symm.trans
            ((congrArg (fun z => TupleRefinement.map T F G ρ α a t ≫ z) hG.symm).trans
              (Category.assoc _ _ _).symm)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement
