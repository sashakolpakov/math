import OAI.ArithmeticGeometry.Models.SpreadingOut.Graph
import OAI.ArithmeticGeometry.Models.SpreadingOut.LocalClosure

/-! # Graph Closure -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GraphClosure.Construction

noncomputable section

/-! Closure of a rational graph in a proper ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {U X P : Over S}

def rationalGraph (j : U ⟶ X) (a : U ⟶ P) :
    U.left ⟶ pullback X.hom P.hom :=
  pullback.lift j.left a.left (j.w.trans a.w.symm)

@[reassoc (attr := simp)]
theorem rationalGraph_fst (j : U ⟶ X) (a : U ⟶ P) :
    rationalGraph j a ≫ pullback.fst X.hom P.hom = j.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rationalGraph_snd (j : U ⟶ X) (a : U ⟶ P) :
    rationalGraph j a ≫ pullback.snd X.hom P.hom = a.left :=
  pullback.lift_snd _ _ _

theorem rationalGraph_immersion (j : U ⟶ X) (a : U ⟶ P) [IsOpenImmersion j.left] :
    IsImmersion (rationalGraph j a) := by
  have : IsImmersion (rationalGraph j a ≫ pullback.fst X.hom P.hom) := by
    rw [rationalGraph_fst]
    infer_instance
  exact IsImmersion.of_comp (rationalGraph j a) (pullback.fst X.hom P.hom)

def graphClosure (j : U ⟶ X) (a : U ⟶ P) : Over S :=
  Over.mk ((rationalGraph j a).imageι ≫ pullback.fst X.hom P.hom ≫ X.hom)

def graphClosureToX (j : U ⟶ X) (a : U ⟶ P) : graphClosure j a ⟶ X :=
  Over.homMk ((rationalGraph j a).imageι ≫ pullback.fst X.hom P.hom) (by
    exact Category.assoc _ _ _)

def graphClosureToP (j : U ⟶ X) (a : U ⟶ P) : graphClosure j a ⟶ P :=
  Over.homMk ((rationalGraph j a).imageι ≫ pullback.snd X.hom P.hom) (by
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f ↦ (rationalGraph j a).imageι ≫ f)
        (pullback.condition (f := X.hom) (g := P.hom)).symm))

def graphClosureLift (j : U ⟶ X) (a : U ⟶ P) : U ⟶ graphClosure j a :=
  Over.homMk (rationalGraph j a).toImage (by
    change (rationalGraph j a).toImage ≫
      ((rationalGraph j a).imageι ≫ pullback.fst X.hom P.hom ≫ X.hom) = U.hom
    rw [← Category.assoc, (rationalGraph j a).toImage_imageι,
      ← Category.assoc, rationalGraph_fst, j.w])

@[reassoc (attr := simp)]
theorem graphClosureLift_toX (j : U ⟶ X) (a : U ⟶ P) :
    (graphClosureLift j a).left ≫ (graphClosureToX j a).left = j.left := by
  change (rationalGraph j a).toImage ≫
    ((rationalGraph j a).imageι ≫ pullback.fst X.hom P.hom) = j.left
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, rationalGraph_fst]

@[reassoc (attr := simp)]
theorem graphClosureLift_toP (j : U ⟶ X) (a : U ⟶ P) :
    (graphClosureLift j a).left ≫ (graphClosureToP j a).left = a.left := by
  change (rationalGraph j a).toImage ≫
    ((rationalGraph j a).imageι ≫ pullback.snd X.hom P.hom) = a.left
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, rationalGraph_snd]

theorem graphClosureToX_proper (j : U ⟶ X) (a : U ⟶ P) [IsProper P.hom] :
    IsProper (graphClosureToX j a).left := by
  change IsProper ((rationalGraph j a).imageι ≫ pullback.fst X.hom P.hom)
  infer_instance

theorem graphClosureToX_surjective (j : U ⟶ X) (a : U ⟶ P)
    [IsDominant j.left] [IsProper P.hom] : Surjective (graphClosureToX j a).left := by
  have hd : IsDominant ((graphClosureLift j a).left ≫ (graphClosureToX j a).left) := by
    rw [graphClosureLift_toX]
    infer_instance
  have := hd
  have : IsDominant (graphClosureToX j a).left :=
    IsDominant.of_comp (graphClosureLift j a).left (graphClosureToX j a).left
  have := graphClosureToX_proper j a
  infer_instance

theorem graphClosure_reduced (j : U ⟶ X) (a : U ⟶ P)
    [QuasiCompact (rationalGraph j a)] [IsReduced U.left] :
    IsReduced (graphClosure j a).left := Image.Construction.schematic_image_reduced (rationalGraph j a)

theorem graphClosureLift_dense_open (j : U ⟶ X) (a : U ⟶ P)
    [IsOpenImmersion j.left] [QuasiCompact (rationalGraph j a)] :
    IsOpenImmersion (graphClosureLift j a).left ∧
      IsDominant (graphClosureLift j a).left := by
  have := rationalGraph_immersion j a
  exact ⟨inferInstanceAs (IsOpenImmersion (rationalGraph j a).toImage),
    inferInstanceAs (IsDominant (rationalGraph j a).toImage)⟩

theorem graphClosure_proper (j : U ⟶ X) (a : U ⟶ P)
    [IsProper X.hom] [IsProper P.hom] : IsProper (graphClosure j a).hom := by
  have := graphClosureToX_proper j a
  rw [← (graphClosureToX j a).w]
  infer_instance

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GraphClosure.Construction
