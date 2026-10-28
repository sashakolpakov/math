import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductGroupIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.EndomorphismReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Product Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductAction

noncomputable section

section

/-! A normalized group-product isomorphism intertwines every actual
group endomorphism with the constant endomorphism from its special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (X : Over (Spec (.of (DualNumber ℂ)))) [GrpObj X]
    [Smooth ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    [IsProper ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    [GeometricallyConnected ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    (e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X))
    [IsMonHom e.hom]

theorem normalizedGroupDualProduct_endomorphism (he : OpenProductData.NormalizesDualProductFiber ℂ e)
    (u : X ⟶ X) [IsMonHom u] :
    u ≫ e.hom = e.hom ≫ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).map ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).map u) := by
  let F := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)
  let A := G.obj X
  have hr : G.map (e.inv ≫ u ≫ e.hom) = G.map (F.map (G.map u)) :=
    NormalizedProduct.EndomorphismReduction.normalizedProductEndomorphism_reduction F G (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) X e he u
  have hp : η[F.obj A] ≫ (e.inv ≫ u ≫ e.hom) = η[F.obj A] ≫ F.map (G.map u) := by
    rw [IsMonHom.one_hom (e.inv ≫ u ≫ e.hom), IsMonHom.one_hom (F.map (G.map u))]
  have h := DualPullbackMorphismRigidity.properDualPullbackMorphism_ext A A (e.inv ≫ u ≫ e.hom) (F.map (G.map u)) hr hp
  apply (cancel_epi e.inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact h

end

/-! Normalized group products intertwine every element of the actual
integral endomorphism action with its constant special-fiber action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of (DualNumber ℂ))))
    (ρ : ActionData.IntegralAction R A)
    (e : A.scheme ≅ ((A.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [hm : IsMonHom e.hom]

theorem normalizedDualProduct_action (he : OpenProductData.NormalizesDualProductFiber ℂ e) (a : R) :
    ρ.map a ≫ e.hom = e.hom ≫ ((ρ.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).map a := by
  have : Smooth ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.scheme).hom :=
    inferInstanceAs (Smooth (A.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have : IsProper ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.scheme).hom :=
    inferInstanceAs (IsProper (A.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have : GeometricallyConnected ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.scheme).hom :=
    inferInstanceAs (GeometricallyConnected (A.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  exact @normalizedGroupDualProduct_endomorphism A.scheme _ _ _ _ e hm he (ρ.map a) (ρ.preservesGroup a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductAction
