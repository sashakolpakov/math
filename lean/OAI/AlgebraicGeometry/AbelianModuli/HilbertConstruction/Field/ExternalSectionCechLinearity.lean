import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.OpenSectionsRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CechTupleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison

/-! # External Section Cech Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalSectionCechLinearity

noncomputable section

/-! The Cech section comparison for an external tensor bundle is an
isomorphism over the original coefficient ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

def fieldExternalSectionsCechModuleIso :
    ((tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf)).mapHomologicalComplex
      (.up ℕ)).obj (Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom N.sheaf U) ≅
    Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom
      ((Scheme.Modules.pushforward b).obj (((L.pullback a).tensor (N.pullback b)).sheaf)) U := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf
  let T := tensorRight B
  let F := Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf ⋙ T
  let E := ((L.pullback a).tensor (N.pullback b)).sheaf
  let G := (Opens.map b.base).op ⋙ Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f.appTop.hom) E
  let W (p : ℕ) (i : Fin (p + 1) → κ) : Y.Opens := ∏ᶜ fun j => U (i j)
  have hW (p : ℕ) (i : Fin (p + 1) → κ) : IsAffineOpen (W p i) := Affine.CechIntersections.affine_cechIntersection U haU p i
  let eW (p : ℕ) (i : Fin (p + 1) → κ) :
      (Scheme.Modules.pullback (W p i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (W p i).toScheme :=
    N.frameRestrict (leOfHom (Pi.π (fun j : Fin (p + 1) => U (i j)) 0)) (heU (i 0)).some
  let e (p : ℕ) (i : Fin (p + 1) → κ) : F.obj (op (W p i)) ≅ G.obj (op (W p i)) :=
    External.OpenSectionsLinearity.externalOpenSectionsModuleIso H L N (W p i) (hW p i) (eW p i) V hV haV heV
  let he (p : ℕ) (j : Fin (p + 2)) (i : Fin (p + 2) → κ) :=
    External.OpenSectionsRestriction.externalOpenSectionsModuleIso_restrict H L N
      (W p (i ∘ (SimplexCategory.δ j).toOrderHom.toFun))
      (hW p (i ∘ (SimplexCategory.δ j).toOrderHom.toFun))
      (eW p (i ∘ (SimplexCategory.δ j).toOrderHom.toFun))
      V hV haV heV (W (p + 1) i) (hW (p + 1) i) (eW (p + 1) i)
      (Cech.SheafCofaces.IntrinsicCech.cechTupleLE U p j i)
  let eBase := eqToIso (congrArg (fun c => (Opens.map b.base).op ⋙ Coefficient.ModulePresheaf.coefficientModulePresheaf c E)
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm)
  let eP := eBase ≪≫ (Coefficient.PushforwardModuleComparison.coefficientPushforwardModuleIso b g.appTop.hom E).symm
  have result := HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso T (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf) U ≪≫
    Module.CechTupleComparison.moduleCechComplexIsoOfTupleIsos U e he ≪≫ (cechComplexFunctor U).mapIso eP
  exact result

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalSectionCechLinearity
