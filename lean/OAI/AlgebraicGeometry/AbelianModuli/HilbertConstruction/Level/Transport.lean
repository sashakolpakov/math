import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Transport of full levels through group-scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {S S' S'' : Scheme.{u}}
variable {A B : Abelian.Schemes.AbelianScheme g S}

instance Abelian.Schemes.AbelianScheme.pullbackCompIso_symm_preservesGroup (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') : IsMonHom (A.pullbackCompIso f h).symm.hom :=
  inferInstanceAs (IsMonHom (A.pullbackCompIso f h).inv)

/-- Equal base morphisms give canonically isomorphic pulled-back group schemes. -/
def Abelian.Schemes.AbelianScheme.pullbackCongrIso (A : Abelian.Schemes.AbelianScheme g S) (f h : S' ⟶ S) (w : f = h) :
    (A.pullback f).scheme ≅ (A.pullback h).scheme :=
  eqToIso (congrArg (fun a => (A.pullback a).scheme) w)

instance Abelian.Schemes.AbelianScheme.pullbackCongrIso_preservesGroup (A : Abelian.Schemes.AbelianScheme g S)
    (f h : S' ⟶ S) (w : f = h) : IsMonHom (A.pullbackCongrIso f h w).hom := by
  cases w
  exact inferInstanceAs (IsMonHom (𝟙 (A.pullback f).scheme))

/-- An isomorphism of abelian schemes identifies their torsion points. -/
def Abelian.Schemes.AbelianScheme.torsionPointsIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (N : ℕ) (T : Over S) :
    A.torsionPoints N T ≃* B.torsionPoints N T where
  toFun x := ⟨x.val ≫ e.hom, by
    change (x.val ≫ e.hom) ^ N = 1
    rw [← MonObj.pow_comp, (A.mem_torsionPoints N T x.val).mp x.property, MonObj.one_comp]⟩
  invFun x := ⟨x.val ≫ e.inv, by
    change (x.val ≫ e.inv) ^ N = 1
    rw [← MonObj.pow_comp, (B.mem_torsionPoints N T x.val).mp x.property, MonObj.one_comp]⟩
  left_inv x := Subtype.ext ((Category.assoc _ _ _).trans
    ((congrArg (fun a => x.val ≫ a) e.hom_inv_id).trans (Category.comp_id _)))
  right_inv x := Subtype.ext ((Category.assoc _ _ _).trans
    ((congrArg (fun a => x.val ≫ a) e.inv_hom_id).trans (Category.comp_id _)))
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val e.hom)

/-- The identification of torsion points is natural in the test scheme. -/
def Abelian.Schemes.AbelianScheme.torsionFunctorIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (N : ℕ) :
    A.torsionFunctor N ≅ B.torsionFunctor N :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (Abelian.Schemes.AbelianScheme.torsionPointsIso e N T.unop)) (by
    intro T U h
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.assoc h.unop x.val e.hom)

/-- Transport an ordered full level across an isomorphism of abelian schemes. -/
def Abelian.Schemes.AbelianScheme.FullLevel.transport (level : A.FullLevel N) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : B.FullLevel N :=
  level ≪≫ Abelian.Schemes.AbelianScheme.torsionFunctorIso e N

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_basis (level : A.FullLevel N) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (T : Over S) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    ((level.transport e).hom.app (.op T) c).val = (level.hom.app (.op T) c).val ≫ e.hom := rfl

/-- Equality of full levels is detected on every ordered torsion basis. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.ext_basis {level₁ level₂ : A.FullLevel N}
    (h : ∀ (T : Over S) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (level₁.hom.app (.op T) c).val = (level₂.hom.app (.op T) c).val) : level₁ = level₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  exact Subtype.ext (h T.unop c)

/-- Simultaneous transport preserves the change of ordered labels between two levels. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.changeEquiv_transport (base level : A.FullLevel N)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (base.transport e).changeEquiv (level.transport e) = base.changeEquiv level := by
  apply Iso.ext
  let t := Abelian.Schemes.AbelianScheme.torsionFunctorIso e N
  change (level.hom ≫ t.hom) ≫ (t.inv ≫ base.inv) = level.hom ≫ base.inv
  exact (Category.assoc _ _ _).trans
    (congrArg (fun a => level.hom ≫ a) (t.hom_inv_id_assoc base.inv))

/-- Simultaneous transport preserves the locally constant level parameters. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_transport [NeZero N] (base level : A.FullLevel N)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (base.transport e).labelsEquiv (level.transport e) = base.labelsEquiv level :=
  congrArg Constant.GroupIsomorphisms.constantGroupIsoLabels (Abelian.Schemes.AbelianScheme.FullLevel.changeEquiv_transport base level e)

/-- Pullback respects equality of the base morphisms, including the level structure. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_pullbackCongr (level : A.FullLevel N) (f h : S' ⟶ S) (w : f = h) :
    (level.pullback f).transport (A.pullbackCongrIso f h w) = level.pullback h := by
  cases w
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  exact Category.comp_id _

/-- Composition pullback becomes literal equality after transporting across its comparison. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_pullbackComp (level : A.FullLevel N) (f : S' ⟶ S) (h : S'' ⟶ S') :
    (((level.pullback f).pullback h).transport (A.pullbackCompIso f h).symm) =
      level.pullback (h ≫ f) := by
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  exact level.pullback_comp_basis f h T c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
