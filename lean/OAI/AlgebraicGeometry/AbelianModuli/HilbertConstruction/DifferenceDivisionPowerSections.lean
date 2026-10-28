import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalarMorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmbeddingPowerMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LineBundleSections

/-! # Difference Division Power Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Dividing a polarized automorphism difference by n identifies its pulled-back embedding bundle with the n-squared power of the divisor's pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def Line.Bundles.LineBundle.factorPowerPullbackIso (L : Line.Bundles.LineBundle Y) (f : X ⟶ Y) (m : Y ⟶ Y)
    (h : X ⟶ Y) (hh : f ≫ m = h) (r : ℕ)
    (e : (L.pullback m).sheaf ≅ (L.tensorPower r).sheaf) :
    (L.pullback h).sheaf ≅ ((L.pullback f).tensorPower r).sheaf :=
  (Scheme.Modules.pullbackCongr hh.symm).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp f m).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ L.powerBaseChangeIso f r

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable {T : Scheme.{u}} (i : T ⟶ A.abelian.scheme.left)

def Moduli.Isomorphisms.LevelPreservingIso.differenceDivisionPowerBundleIso (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (n : ℕ) (d : A.abelian.EndRing) (hd : n • d = e.endRingUnit.val - 1) :
    (E.power.pullback (i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)).sheaf ≅
      ((E.power.pullback (i ≫ d.toMul.hom.hom.left)).tensorPower (n * n)).sheaf :=
  E.power.factorPowerPullbackIso (i ≫ d.toMul.hom.hom.left) (A.abelian.multiplication n).left
    (i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)
    ((Category.assoc _ _ _).trans (congrArg (fun f => i ≫ f)
      (congrArg Over.Hom.left (e.difference_factor_of_nsmul n d hd))))
    (n * n) (A.embeddingPower_multiplication_iso E n)

def Moduli.Isomorphisms.LevelPreservingIso.differenceDivisionPowerSectionsIso (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (n : ℕ) (d : A.abelian.EndRing) (hd : n • d = e.endRingUnit.val - 1) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
      (E.power.pullback (i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)).sheaf ≃ₗ[K]
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
      ((E.power.pullback (i ≫ d.toMul.hom.hom.left)).tensorPower (n * n)).sheaf :=
  Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso (i ≫ A.abelian.scheme.hom) (e.differenceDivisionPowerBundleIso A E i n d hd)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
