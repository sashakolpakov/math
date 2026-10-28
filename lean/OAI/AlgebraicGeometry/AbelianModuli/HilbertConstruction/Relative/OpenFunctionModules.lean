import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf

/-! # Open Function Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules

noncomputable section

/-! Regular functions on a smaller open are modules over the functions on a larger open, with linear restriction maps. These are the local modules used to assemble homogeneous frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def relativeOpenFunctionModule (V W : X.Opens) (h : W ≤ V) : ModuleCat.{u} Γ(X, V) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj (ModuleCat.of Γ(X, W) Γ(X, W))

def relativeOpenFunctionRestriction (V : X.Opens) {W Z : X.Opens}
    (hW : W ≤ V) (hZ : Z ≤ V) (a : Z ≤ W) :
    relativeOpenFunctionModule V W hW ⟶ relativeOpenFunctionModule V Z hZ := by
  exact ModuleCat.ofHom (X := relativeOpenFunctionModule V W hW)
    (Y := relativeOpenFunctionModule V Z hZ) {
    toFun := X.presheaf.map (homOfLE a).op
    map_add' := map_add _
    map_smul' := fun r s => by
      change X.presheaf.map (homOfLE a).op
        (@Mul.mul Γ(X, W) inferInstance (X.presheaf.map (homOfLE hW).op r) s) =
          @Mul.mul Γ(X, Z) inferInstance (X.presheaf.map (homOfLE hZ).op r)
            (X.presheaf.map (homOfLE a).op s)
      have hm := (X.presheaf.map (homOfLE a).op).hom.map_mul
        (X.presheaf.map (homOfLE hW).op r) s
      exact hm.trans (congrArg (fun z : Γ(X, Z) => z * (X.presheaf.map (homOfLE a).op s))
        (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE hW).op (homOfLE a).op) r).symm) }

theorem relativeOpenFunctionRestriction_refl (V W : X.Opens) (h : W ≤ V) :
    relativeOpenFunctionRestriction V h h (le_refl W) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (.op W)) x

theorem relativeOpenFunctionRestriction_comp (V : X.Opens) {W Z Q : X.Opens}
    (hW : W ≤ V) (hZ : Z ≤ V) (hQ : Q ≤ V) (a : Z ≤ W) (b : Q ≤ Z) :
    relativeOpenFunctionRestriction V hW hZ a ≫ relativeOpenFunctionRestriction V hZ hQ b =
      relativeOpenFunctionRestriction V hW hQ (b.trans a) := by
  apply ModuleCat.hom_ext
  ext x
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE a).op (homOfLE b).op) x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules
