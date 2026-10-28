import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmbientComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel

/-! # Generic Ambient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GenericAmbientPullback.Construction

noncomputable section

/-!
The represented ambient family agrees with the ordinary pullback for
every commutative group scheme, including finite torsion blocks. The
comparison preserves the actual point-group laws.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (P : Over S)

def nativeAmbientPullbackIso :
    (Kernel.Inclusion.Construction.ambientGroupScheme G.X P).X ≅ ((Over.pullback P.hom).mapGrp.obj G).X :=
  Over.isoMk (pullbackSymmetry P.hom G.X.hom) (pullbackSymmetry_hom_comp_snd P.hom G.X.hom)

theorem nativeAmbientPullbackIso_points (U : Over P.left) (x : U ⟶ (Kernel.Inclusion.Construction.ambientGroupScheme G.X P).X) :
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm (x ≫ (nativeAmbientPullbackIso G P).hom) =
      AmbientComparison.Construction.ambientPointMulEquiv G.X P U x := by
  apply Over.OverMorphism.ext
  rw [AmbientComparison.Construction.ambientPointMulEquiv_left]
  change (x.left ≫ (pullbackSymmetry P.hom G.X.hom).hom) ≫ pullback.fst G.X.hom P.hom =
    x.left ≫ pullback.snd P.hom G.X.hom
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => x.left ≫ k) (pullbackSymmetry_hom_comp_fst P.hom G.X.hom))

instance nativeAmbientPullbackIso_isMonHom : IsMonHom (nativeAmbientPullbackIso G P).hom := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro U
    apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.injective
    exact (nativeAmbientPullbackIso_points G P U 1).trans
      ((AmbientComparison.Construction.ambientPointMulEquiv G.X P U).map_one.trans (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.map_one.symm)
  · intro U x y
    apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.injective
    exact (nativeAmbientPullbackIso_points G P U (x * y)).trans
      (((AmbientComparison.Construction.ambientPointMulEquiv G.X P U).map_mul x y).trans
        ((congrArg₂ (fun a b : (Over.map P.hom).obj U ⟶ G.X => a * b)
          (nativeAmbientPullbackIso_points G P U x).symm
          (nativeAmbientPullbackIso_points G P U y).symm).trans
            ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.map_mul
              (x ≫ (nativeAmbientPullbackIso G P).hom) (y ≫ (nativeAmbientPullbackIso G P).hom)).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GenericAmbientPullback.Construction
