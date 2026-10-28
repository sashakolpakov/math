import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointExternalSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyRetraction

/-! # Point Cohomology Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Addition embeds the actual cohomology of a Poincare point bundle in that of its external tensor square. The retraction is the zero-section graph. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)
variable (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme)

def Dual.Data.DualAbelianData.poincarePointBundle_externalSquareCohomologyMap (n : ℕ) :
    Zariski.Cohomology.ZariskiCohomology.H (D.poincarePointBundle f).sheaf n →+
      Zariski.Cohomology.ZariskiCohomology.H (Graph.ExternalTensorBundle.externalTensorBundle (A := A.scheme) (B := A.scheme)
        (D.poincarePointBundle f) (D.poincarePointBundle f)).sheaf n :=
  ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.scheme ⊗ A.scheme).left n).map
    (D.poincarePointBundle_additionIso f).hom).hom.comp
      (Zariski.CohomologyPullbackMap.ZariskiCohomology.pullbackMap
        (fst A.scheme A.scheme * snd A.scheme A.scheme).left (D.poincarePointBundle f).sheaf n)

theorem Dual.Data.DualAbelianData.poincarePointBundle_externalSquareCohomologyMap_injective (n : ℕ) :
    Function.Injective (D.poincarePointBundle_externalSquareCohomologyMap f n) := by
  let m := fst A.scheme A.scheme * snd A.scheme A.scheme
  let s := lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)
  have hs : s.left ≫ m.left = 𝟙 A.scheme.left :=
    congrArg Over.Hom.left A.addition_section
  have hp := Zariski.CohomologyRetraction.ZariskiCohomology.pullbackMap_injective_of_section m.left s.left hs
    (D.poincarePointBundle f).sheaf n
  have he := (ConcreteCategory.bijective_of_isIso
    ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.scheme ⊗ A.scheme).left n).map
      (D.poincarePointBundle_additionIso f).hom)).injective
  exact he.comp hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
