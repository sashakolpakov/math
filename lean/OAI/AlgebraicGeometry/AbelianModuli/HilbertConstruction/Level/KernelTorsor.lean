import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelTorsor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Isogeny
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison

/-! # Kernel Torsor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full level makes the self-pullback of multiplication a product with the actual constant level scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.fullLevelKernelTorsorIso (level : A.FullLevel n) :
    A.scheme ⊗ Level.Scheme.constantFullLevelScheme g n S ≅ Limits.pullback (A.multiplication n) (A.multiplication n) :=
  (Iso.refl A.scheme ⊗ᵢ level.schemeIso) ≪≫ (A.fullLevelMultiplicationIsogeny level).kernelTorsorIso

@[reassoc]
theorem Abelian.Schemes.AbelianScheme.fullLevelKernelTorsorIso_fst (level : A.FullLevel n) :
    (A.fullLevelKernelTorsorIso level).hom ≫ Limits.pullback.fst (A.multiplication n) (A.multiplication n) =
      fst A.scheme (Level.Scheme.constantFullLevelScheme g n S) := by
  let p := A.fullLevelMultiplicationIsogeny level
  let e : Level.Scheme.constantFullLevelScheme g n S ≅ p.kernelScheme := level.schemeIso
  let t := 𝟙 A.scheme ⊗ₘ e.hom
  change (t ≫ p.kernelActionPair) ≫ Limits.pullback.fst p.hom p.hom = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => t ≫ k) p.kernelActionPair_fst).trans
      ((tensorHom_fst (𝟙 A.scheme) e.hom).trans (Category.comp_id _)))

@[reassoc]
theorem Abelian.Schemes.AbelianScheme.fullLevelKernelTorsorIso_snd (level : A.FullLevel n) :
    (A.fullLevelKernelTorsorIso level).hom ≫ Limits.pullback.snd (A.multiplication n) (A.multiplication n) =
      fst A.scheme (Level.Scheme.constantFullLevelScheme g n S) *
        (snd A.scheme (Level.Scheme.constantFullLevelScheme g n S) ≫ level.schemeIso.hom ≫ A.torsionInclusion n) := by
  let p := A.fullLevelMultiplicationIsogeny level
  let e : Level.Scheme.constantFullLevelScheme g n S ≅ p.kernelScheme := level.schemeIso
  let t := 𝟙 A.scheme ⊗ₘ e.hom
  have hf : t ≫ fst A.scheme p.kernelScheme = fst A.scheme (Level.Scheme.constantFullLevelScheme g n S) :=
    (tensorHom_fst (𝟙 A.scheme) e.hom).trans (Category.comp_id _)
  have hs : t ≫ (snd A.scheme p.kernelScheme ≫ p.kernelInclusion) =
      snd A.scheme (Level.Scheme.constantFullLevelScheme g n S) ≫ level.schemeIso.hom ≫ A.torsionInclusion n :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ p.kernelInclusion) (tensorHom_snd (𝟙 A.scheme) e.hom)).trans
        (Category.assoc _ _ _))
  change (t ≫ p.kernelActionPair) ≫ Limits.pullback.snd p.hom p.hom = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun k => t ≫ k) p.kernelActionPair_snd).trans
    ((MonObj.comp_mul _ _ _).trans (congrArg₂ (fun a b => a * b) hf hs)))

def Abelian.Schemes.AbelianScheme.fullLevelKernelTorsorSchemeIso (level : A.FullLevel n) :
    (A.scheme ⊗ Level.Scheme.constantFullLevelScheme g n S).left ≅
      Limits.pullback (A.multiplication n).left (A.multiplication n).left :=
  (Over.forget S).mapIso (A.fullLevelKernelTorsorIso level) ≪≫ HilbertConstruction.Over.DiagonalComparison.overSelfPullbackIso (A.multiplication n)

@[reassoc]
theorem Abelian.Schemes.AbelianScheme.fullLevelKernelTorsorSchemeIso_fst (level : A.FullLevel n) :
    (A.fullLevelKernelTorsorSchemeIso level).hom ≫
      Limits.pullback.fst (A.multiplication n).left (A.multiplication n).left =
        Limits.pullback.fst A.scheme.hom (Level.Scheme.constantFullLevelScheme g n S).hom := by
  have h := ((IsPullback.of_hasPullback (A.multiplication n) (A.multiplication n)).map (Over.forget S)).isoPullback_hom_fst
  change ((A.fullLevelKernelTorsorIso level).hom.left ≫ (HilbertConstruction.Over.DiagonalComparison.overSelfPullbackIso (A.multiplication n)).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun k => (A.fullLevelKernelTorsorIso level).hom.left ≫ k) h).trans
    (congrArg Over.Hom.left (A.fullLevelKernelTorsorIso_fst level)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
