import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Iso Calculus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus

noncomputable section

section

/-! Functorial transport of actual ordered full levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} {g N : ℕ}
    {A B C : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

instance abelianIsoRefl_isMonHom (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    IsMonHom (CategoryTheory.Iso.refl A.scheme).hom :=
  inferInstanceAs (IsMonHom (𝟙 A.scheme))

instance abelianIsoTrans_isMonHom (e : A.scheme ≅ B.scheme) (d : B.scheme ≅ C.scheme)
    [IsMonHom e.hom] [IsMonHom d.hom] : IsMonHom (e ≪≫ d).hom :=
  inferInstanceAs (IsMonHom (e.hom ≫ d.hom))

instance abelianIsoSymm_isMonHom (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)

instance abelianIsoPullback_isMonHom (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (b : T ⟶ S) :
    IsMonHom ((Over.pullback b).mapIso e).hom :=
  inferInstanceAs (IsMonHom ((Over.pullback b).map e.hom))

def abelianPullbackIso (e : A.scheme ≅ B.scheme) (b : T ⟶ S) :
    (A.pullback b).scheme ≅ (B.pullback b).scheme := (Over.pullback b).mapIso e

instance abelianPullbackIso_isMonHom (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (b : T ⟶ S) :
    IsMonHom (abelianPullbackIso e b).hom :=
  inferInstanceAs (IsMonHom ((Over.pullback b).map e.hom))

theorem fullLevel_transport_refl (α : A.FullLevel N) :
    α.transport (B := A) (Iso.refl A.scheme) = α := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  exact Category.comp_id _

theorem fullLevel_transport_trans (α : A.FullLevel N)
    (e : A.scheme ≅ B.scheme) (d : B.scheme ≅ C.scheme) [IsMonHom e.hom] [IsMonHom d.hom] :
    (α.transport (B := B) e).transport (B := C) d =
      α.transport (B := C) (e ≪≫ d) := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  exact Category.assoc _ _ _

theorem fullLevel_transport_symm (α : A.FullLevel N)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (α.transport (B := B) e).transport (B := A) e.symm = α := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (α.hom.app (.op U) c).val ≫ z) e.hom_inv_id).trans (Category.comp_id _))

theorem fullLevel_transport_injective (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Function.Injective (fun α : A.FullLevel N => α.transport (B := B) e) := by
  intro α β h
  have hh := congrArg (fun γ : B.FullLevel N => γ.transport (B := A) e.symm) h
  exact (fullLevel_transport_symm α e).symm.trans (hh.trans (fullLevel_transport_symm β e))

theorem fullLevel_transport_pullback (α : A.FullLevel N)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (b : T ⟶ S) :
    (α.transport (B := B) e).pullback b = (α.pullback b).transport
      (B := B.pullback b) (abelianPullbackIso e b) := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  apply (B.baseChangePointsEquiv b U).injective
  rw [HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.pullback_basis, HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport_basis]
  change (α.hom.app (.op ((Over.map b).obj U)) c).val ≫ e.hom =
    B.baseChangePointsEquiv b U
      (((α.pullback b).hom.app (.op U) c).val ≫ (Over.pullback b).map e.hom)
  rw [HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map, HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.pullback_basis]

end

/-! Relabeling ordered levels commutes with actual scheme pullback and
group-isomorphism transport, including on disconnected test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} {g N : ℕ} {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} [NeZero N]

def relabelFullLevel (α : A.FullLevel N) (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g N)) :
    A.FullLevel N := α.labelsEquiv.symm b

theorem relabelFullLevel_one (α : A.FullLevel N) : relabelFullLevel α 1 = α := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V c
  rfl

theorem relabelFullLevel_mul (α : A.FullLevel N)
    (b c : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g N)) :
    relabelFullLevel (relabelFullLevel α b) c = relabelFullLevel α (b * c) := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V d
  rfl

theorem relabelFullLevel_pullback (α : A.FullLevel N)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g N)) (f : T ⟶ S) :
    (relabelFullLevel α b).pullback f =
      relabelFullLevel (α.pullback f) (b.comap ⟨f, f.continuous⟩) := by
  apply (α.pullback f).labelsEquiv.injective
  exact (HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_pullback α (relabelFullLevel α b) f).trans
    ((congrArg (fun c : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g N) =>
      c.comap ⟨f, f.continuous⟩) (α.labelsEquiv.apply_symm_apply b)).trans
      ((α.pullback f).labelsEquiv.apply_symm_apply _).symm)

theorem relabelFullLevel_transport (α : A.FullLevel N)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g N)) (e : A.scheme ≅ B.scheme)
    [IsMonHom e.hom] :
    (relabelFullLevel α b).transport e = relabelFullLevel (α.transport e) b := by
  apply (α.transport e).labelsEquiv.injective
  exact (HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_transport α (relabelFullLevel α b) e).trans
    ((α.labelsEquiv.apply_symm_apply b).trans
      ((α.transport e).labelsEquiv.apply_symm_apply b).symm)

theorem relabelFullLevel_transport_eq (α : A.FullLevel N) (β : B.FullLevel N)
    (b : LocallyConstant S (HilbertConstruction.Level.Parameters.LevelLabelAut g N)) (e : A.scheme ≅ B.scheme)
    [IsMonHom e.hom] (h : α.transport e = β) :
    (relabelFullLevel α b).transport e = relabelFullLevel β b :=
  (relabelFullLevel_transport α b e).trans (congrArg (fun a => relabelFullLevel a b) h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus
