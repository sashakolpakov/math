import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-! # Descent Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentIso

noncomputable section

/-! Original-base tests construct actual isomorphisms of ordinary descent data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
  (D E : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left))
  (e : D.obj PUnit.unit ≅ E.obj PUnit.unit)

/-- The quotient point gives every scheme test a structure map to the original base. -/
def iso_of_over
    (h : ∀ (T : Over S) (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x.left).map e.hom ≫ E.hom q.left
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      D.hom q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
          (Scheme.Modules.pullback y.left).map e.hom) : D ≅ E :=
  Pseudofunctor.DescentData.isoMk (fun _ => e) (by
    intro T q i j x y hx hy
    cases i
    cases j
    let U : Over S := Over.mk (q ≫ B.hom)
    let q' : U ⟶ B := Over.homMk q rfl
    let x' : U ⟶ A := Over.homMk x (by
      change x ≫ A.hom = q ≫ B.hom
      rw [← hx, Category.assoc, Over.w f])
    let y' : U ⟶ A := Over.homMk y (by
      change y ≫ A.hom = q ≫ B.hom
      rw [← hy, Category.assoc, Over.w f])
    exact h U q' x' y' (Over.OverMorphism.ext hx) (Over.OverMorphism.ext hy))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentIso
