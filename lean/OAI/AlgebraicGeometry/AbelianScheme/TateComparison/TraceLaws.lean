import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceAllTests

/-! # Trace Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Additivity and target functoriality of the constructed algebraic
trace. All equalities concern actual scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme.{0}} {X A A' : Over B}
  [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
  (C : Correspondences.EtaleCorrespondence X)

def Correspondences.EtaleCorrespondence.postcompPointHom {T : Over B} (g : A ⟶ A') [IsMonHom g] : (T ⟶ A) →* (T ⟶ A') where
  toFun f := f ≫ g
  map_one' := MonObj.one_comp g
  map_mul' f h := MonObj.mul_comp f h g

theorem Correspondences.EtaleCorrespondence.geometricTrace_postcomp (f : X ⟶ A) (g : A ⟶ A') [IsMonHom g]
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X) :
    C.geometricTrace (f ≫ g) b x = C.geometricTrace f b x ≫ g := by
  change ((C.neighbors b x).map (fun y => y ≫ (f ≫ g))).prod =
    Correspondences.EtaleCorrespondence.postcompPointHom g (((C.neighbors b x).map (fun y => y ≫ f)).prod)
  rw [map_multiset_prod, Multiset.map_map]
  congr 1

theorem Correspondences.EtaleCorrespondence.geometricTrace_mul (f g : X ⟶ A)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X) :
    C.geometricTrace (f * g) b x = C.geometricTrace f b x * C.geometricTrace g b x := by
  simp only [Correspondences.EtaleCorrespondence.geometricTrace, MonObj.comp_mul, Multiset.prod_map_mul]

variable [IsReduced X.left] [IsLocallyNoetherian X.left] [IsSeparated A.hom]

theorem Correspondences.EtaleCorrespondence.algebraicTrace_mul (f g : X ⟶ A) :
    C.algebraicTrace (f * g) = C.algebraicTrace f * C.algebraicTrace g := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  rw [MonObj.comp_mul, Correspondences.EtaleCorrespondence.algebraicTrace_geometric, Correspondences.EtaleCorrespondence.algebraicTrace_geometric,
    Correspondences.EtaleCorrespondence.algebraicTrace_geometric, Correspondences.EtaleCorrespondence.geometricTrace_mul]

theorem Correspondences.EtaleCorrespondence.algebraicTrace_one : C.algebraicTrace (1 : X ⟶ A) = 1 := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  rw [Correspondences.EtaleCorrespondence.algebraicTrace_geometric, MonObj.comp_one]
  simp [Correspondences.EtaleCorrespondence.geometricTrace, MonObj.comp_one]

def Correspondences.EtaleCorrespondence.algebraicTraceHom : (X ⟶ A) →* (X ⟶ A) where
  toFun := C.algebraicTrace
  map_one' := C.algebraicTrace_one
  map_mul' := C.algebraicTrace_mul

theorem Correspondences.EtaleCorrespondence.algebraicTrace_div (f g : X ⟶ A) :
    C.algebraicTrace (f / g) = C.algebraicTrace f / C.algebraicTrace g :=
  (C.algebraicTraceHom).map_div f g

theorem Correspondences.EtaleCorrespondence.algebraicTrace_postcomp [IsSeparated A'.hom]
    (f : X ⟶ A) (g : A ⟶ A') [IsMonHom g] :
    C.algebraicTrace (f ≫ g) = C.algebraicTrace f ≫ g := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  rw [← Category.assoc, Correspondences.EtaleCorrespondence.algebraicTrace_geometric, Correspondences.EtaleCorrespondence.algebraicTrace_geometric,
    Correspondences.EtaleCorrespondence.geometricTrace_postcomp]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
