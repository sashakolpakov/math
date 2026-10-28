import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtaleTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleMapsFromPoints

/-! # Active Etale Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtalePoints.Construction

noncomputable section

/-!
Reduced test schemes see exactly the etale factor of the ordinary
active block. This identifies the induced map on the etale plane from
the original native map, and constructs its inverse from geometric
point bijectivity when that bijectivity is available.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
variable {B B' : Grp (Over (Spec (.of k)))}
variable (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B) (e' : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B')

/-- The two coordinate maps are inverse on every reduced test scheme. -/
theorem activeEtaleReduced_projection_inclusion (T : Over (Spec (.of k)))
    [IsReduced T.left] (x : T ⟶ B.X) :
    (x ≫ (ActiveEtaleTransport.Construction.activeEtaleProjection k q e).hom.hom) ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom = x := by
  let M := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1
  let E := EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q
  let t : T ⟶ M.X ⊗ E.X := x ≫ e.hom.hom.hom
  have ht : t ≫ fst M.X E.X = 1 :=
    ReducedHeightOneMaps.Construction.map_from_reduced_of_trivial_frobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) _
      (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k 1)
  have hfac : (t ≫ snd M.X E.X) ≫ (AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom = t := by
    apply CartesianMonoidalCategory.hom_ext
    · change ((t ≫ snd M.X E.X) ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X)) ≫ fst M.X E.X = _
      rw [Category.assoc, lift_fst, MonObj.comp_one]
      exact ht.symm
    · change ((t ≫ snd M.X E.X) ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X)) ≫ snd M.X E.X = _
      rw [Category.assoc, lift_snd, Category.comp_id]
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 B.X :=
    ((Grp.forget _).mapIso e).hom_inv_id
  change (x ≫ (e.hom.hom.hom ≫ snd M.X E.X)) ≫
    ((AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom ≫ e.inv.hom.hom) = x
  rw [← Category.assoc x, ← Category.assoc, hfac, Category.assoc, he, Category.comp_id]

def activeEtaleReducedPointsEquiv (T : Over (Spec (.of k))) [IsReduced T.left] :
    (T ⟶ B.X) ≃* (T ⟶ (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X) where
  toFun x := x ≫ (ActiveEtaleTransport.Construction.activeEtaleProjection k q e).hom.hom
  invFun x := x ≫ (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom
  left_inv := activeEtaleReduced_projection_inclusion k q e T
  right_inv x := by
    have h := congrArg
      (fun z : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ⟶ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q =>
        z.hom.hom) (ActiveEtaleTransport.Construction.chosenActiveEtalePlane_projection k q e)
    change (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ (ActiveEtaleTransport.Construction.activeEtaleProjection k q e).hom.hom = 𝟙 _ at h
    change (x ≫ (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom) ≫
      (ActiveEtaleTransport.Construction.activeEtaleProjection k q e).hom.hom = x
    rw [Category.assoc, h, Category.comp_id]
  map_mul' x y := MonObj.mul_comp x y _

theorem activeEtaleMap_points_bijective (a : B ⟶ B')
    (ha : Function.Bijective ((yonedaGrp.map a).app (op (Over.mk (𝟙 _))))) :
    Function.Bijective ((yonedaGrp.map (ActiveEtaleTransport.Construction.activeEtaleMap k q e e' a)).app
      (op (Over.mk (𝟙 _)))) := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  have : Smooth T.hom := inferInstanceAs (Smooth (𝟙 (Spec (.of k))))
  have : IsReduced T.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field T.hom
  let u := activeEtaleReducedPointsEquiv k q e T
  let v := activeEtaleReducedPointsEquiv k q e' T
  have h := v.bijective.comp (ha.comp u.symm.bijective)
  change Function.Bijective (fun x : T ⟶ (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X =>
    ((x ≫ (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom) ≫ a.hom.hom) ≫
      (ActiveEtaleTransport.Construction.activeEtaleProjection k q e').hom.hom) at h
  change Function.Bijective (fun x : T ⟶ (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X =>
    x ≫ (ActiveEtaleTransport.Construction.activeEtaleMap k q e e' a).hom.hom)
  convert h using 1
  funext x
  exact (Category.assoc x (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom
    (a.hom.hom ≫ (ActiveEtaleTransport.Construction.activeEtaleProjection k q e').hom.hom)).symm.trans
      (congrArg (fun z => z ≫ (ActiveEtaleTransport.Construction.activeEtaleProjection k q e').hom.hom)
        (Category.assoc x (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom a.hom.hom).symm)

/-- The inverse of the actual etale-plane map is constructed from its
proved rational-point bijectivity, with all native maps recovered. -/
def activeEtaleIsoOfPoints (a : B ⟶ B')
    (ha : Function.Bijective ((yonedaGrp.map a).app (op (Over.mk (𝟙 _))))) :
    EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q :=
  EtaleMapsFromPoints.Construction.fieldEtaleIsoOfPoints k (ActiveEtaleTransport.Construction.activeEtaleMap k q e e' a)
    (activeEtaleMap_points_bijective k q e e' a ha)

theorem activeEtaleIsoOfPoints_hom (a : B ⟶ B')
    (ha : Function.Bijective ((yonedaGrp.map a).app (op (Over.mk (𝟙 _))))) :
    (activeEtaleIsoOfPoints k q e e' a ha).hom = ActiveEtaleTransport.Construction.activeEtaleMap k q e e' a :=
  EtaleMapsFromPoints.Construction.fieldEtaleIsoOfPoints_hom k _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtalePoints.Construction
