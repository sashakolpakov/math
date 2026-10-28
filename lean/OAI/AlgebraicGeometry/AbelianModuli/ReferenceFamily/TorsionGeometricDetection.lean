import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionFunctoriality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Torsion Geometric Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionGeometricDetection

noncomputable section

/-! Equality of maps on geometric fibers detects their action on the
finite-etale torsion scheme over an arbitrary, possibly nonreduced base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S T : Scheme.{0}} {A B : Over S}

theorem points_eq_of_pullback_map_eq (s : T ⟶ S) (f h : A ⟶ B)
    (he : (Over.pullback s).map f = (Over.pullback s).map h)
    (x : Over.mk s ⟶ A) : x ≫ f = x ≫ h := by
  let U : Over T := Over.mk (𝟙 T)
  let y : (Over.map s).obj U ⟶ A := Over.homMk x.left (by
    change x.left ≫ A.hom = 𝟙 T ≫ s
    exact x.w.trans (Category.id_comp s).symm)
  have hh : y ≫ f = y ≫ h := by
    apply ((Over.mapPullbackAdj s).homEquiv U B).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right, he]
  exact Over.OverMorphism.ext (congrArg (fun z => z.left) hh)

variable {g j N : ℕ} (C : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : HilbertConstruction.Abelian.Schemes.AbelianScheme j S)
    [Etale (D.torsionScheme N).hom]

theorem torsionMap_eq_of_geometric_pullbacks
    (f h : C.scheme ⟶ D.scheme) [IsMonHom f] [IsMonHom h]
    (he : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map h) :
    HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap N f = HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap N h := by
  apply AbelianScheme.IsogenyQuotient.Geometric.Points.Construction.etale_ext_of_geometric_points
  intro k hk hclosed s x
  apply (cancel_mono (D.torsionInclusion N)).mp
  simp only [Category.assoc, HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion]
  exact (Category.assoc _ _ _).symm.trans
    ((points_eq_of_pullback_map_eq s f h (he k s) (x ≫ C.torsionInclusion N)).trans
      (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionGeometricDetection
