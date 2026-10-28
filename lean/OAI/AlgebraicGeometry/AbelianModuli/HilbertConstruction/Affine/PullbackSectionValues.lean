import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections

/-! # Pullback Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackSectionValues

noncomputable section

/-! The actual affine pullback section isomorphism sends pure tensors to scalar multiples of the canonical adjunction-unit pullback, and evaluates maps by their adjoints. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (M : X.Modules) [M.IsQuasicoherent]

def affinePullbackUnitSection (x : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x

theorem affinePullbackSections_one (x : Γ(M, ⊤)) :
    (GeometricSections.AffineGeometricSections.iso f M).hom.hom ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x) =
      affinePullbackUnitSection f M x := by
  have h := ConcreteCategory.congr_hom (GeometricSections.AffineGeometricSections.normalization f M) x
  exact (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (GeometricSections.AffineGeometricSections.iso f M).hom x).symm.trans h

theorem affinePullbackSections_tmul (r : Γ(Y, ⊤)) (x : Γ(M, ⊤)) :
    (GeometricSections.AffineGeometricSections.iso f M).hom.hom (r ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x) =
      r • affinePullbackUnitSection f M x := by
  let e := GeometricSections.AffineGeometricSections.iso f M
  let t : (ModuleCat.extendScalars f.appTop.hom).obj
      ((SectionAdjunction.AffineSectionAdjunction.sections X).obj M) :=
    (1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x
  have ht : r • t = r ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x := by
    exact (ModuleCat.ExtendScalars.smul_tmul f.appTop.hom r 1 x).trans
      (congrArg (fun z => z ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x) (mul_one r))
  calc
    e.hom.hom (r ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x) = e.hom.hom (r • t) :=
      congrArg e.hom.hom ht.symm
    _ = r • e.hom.hom t := e.hom.hom.map_smul r t
    _ = _ := congrArg (fun z => r • z) (affinePullbackSections_one f M x)

theorem affinePullbackSections_map_tmul {Q : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ Q) (r : Γ(Y, ⊤)) (x : Γ(M, ⊤)) :
    φ.app ⊤ ((GeometricSections.AffineGeometricSections.iso f M).hom.hom (r ⊗ₜ[Γ(X, ⊤), f.appTop.hom] x)) =
      r • (show Γ(Q, ⊤) from
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M Q φ).app ⊤ x) := by
  rw [affinePullbackSections_tmul, φ.app_smul]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackSectionValues
