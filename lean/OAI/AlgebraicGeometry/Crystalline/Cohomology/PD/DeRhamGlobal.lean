import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site

/-! # De Rham Global -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal

noncomputable section

/-!
# Cohomology: functorial divided-power forms on the crystalline site

Morphisms of divided-power thickenings act on the divided-power de Rham
complex. These restriction maps assemble the local complexes on the actual
crystalline site; sheafification supplies the global complex of sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R]
variable {A B C : CommAlgCat.{u} R}
variable {I : Ideal A} {J : Ideal B} {L : Ideal C}
variable {δI : DividedPowers I} {δJ : DividedPowers J} {δL : DividedPowers L}

theorem ordinaryMap_smul (f : A ⟶ B) (n : ℕ) (a : A)
    (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    DeRhamGlobalId.DeRhamGlobal.formMap f n (a • ω) = f a • DeRhamGlobalId.DeRhamGlobal.formMap f n ω := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  rw [← (DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ.map_smul]
  change (DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ (DeRhamGlobalId.DeRhamGlobal.rawMap f n (a • v)) =
    f a • (DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ (DeRhamGlobalId.DeRhamGlobal.rawMap f n v)
  rw [DeRhamGlobalId.DeRhamGlobal.rawMap_smul, map_smul]

def relationMap (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    {n : ℕ} (r : DeRham.PDDeRham.RelationIndex A I n) : DeRham.PDDeRham.RelationIndex B J n where
  v j := f (r.v j)
  i := r.i
  x := ⟨f r.x, hf.ideal_comp (Ideal.mem_map_of_mem f.hom.toRingHom r.x.property)⟩
  m := r.m

theorem ordinaryMap_relation (f : A ⟶ B)
    (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    {n : ℕ} (r : DeRham.PDDeRham.RelationIndex A I n) :
    DeRhamGlobalId.DeRhamGlobal.formMap f n (DeRham.PDDeRham.relation R A I δI n r) =
      DeRham.PDDeRham.relation R B J δJ n (relationMap f hf r) := by
  simp only [DeRham.PDDeRham.relation, relationMap, map_sub, DeRhamGlobalId.DeRhamGlobal.formMap_symbol,
    map_one, DeRhamGlobalId.DeRhamGlobal.map_tuple_update]
  have hd (m : ℕ) : f (δI.dpow m r.x) = δJ.dpow m (f r.x) := hf.map_dpow r.x.property
  rw [hd, hd]

theorem ordinaryMap_relations (f : A ⟶ B)
    (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    {n : ℕ} (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    (hω : ω ∈ DeRham.PDDeRham.relations R A I δI n) :
    DeRhamGlobalId.DeRhamGlobal.formMap f n ω ∈ DeRham.PDDeRham.relations R B J δJ n := by
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨r, rfl⟩ := hω
    rw [ordinaryMap_relation f hf]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero => simp
  | add ω η hω hη ihω ihη => rw [map_add]; exact Submodule.add_mem _ ihω ihη
  | smul a ω hω ih => rw [ordinaryMap_smul]; exact Submodule.smul_mem _ _ ih

/-- Pullback of divided-power forms along a divided-power algebra map. -/
def formMap (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom) (n : ℕ) :
    DeRham.PDDeRham.Form R A I δI n →ₗ[R] DeRham.PDDeRham.Form R B J δJ n :=
  ((DeRham.PDDeRham.relations R A I δI n).restrictScalars R).liftQ
    (((DeRham.PDDeRham.relations R B J δJ n).mkQ.restrictScalars R).comp (DeRhamGlobalId.DeRhamGlobal.formMap f n))
    (fun ω hω => Submodule.Quotient.mk_eq_zero _ |>.mpr (ordinaryMap_relations f hf ω hω))

@[simp]
theorem formMap_mk (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formMap f hf n ((DeRham.PDDeRham.relations R A I δI n).mkQ ω) =
      (DeRham.PDDeRham.relations R B J δJ n).mkQ (DeRhamGlobalId.DeRhamGlobal.formMap f n ω) := rfl

theorem formMap_smul (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (n : ℕ) (a : A) (ω : DeRham.PDDeRham.Form R A I δI n) :
    formMap f hf n (a • ω) = f a • formMap f hf n ω := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δI n) ω
  rw [← (DeRham.PDDeRham.relations R A I δI n).mkQ.map_smul, formMap_mk,
    ordinaryMap_smul, map_smul, formMap_mk]

@[simp]
theorem formMap_symbol (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (n : ℕ) (a : A) (v : Fin n → A) :
    formMap f hf n (DeRham.PDDeRham.symbol R A I δI a v) =
      DeRham.PDDeRham.symbol R B J δJ (f a) (fun i => f (v i)) := by
  change (DeRham.PDDeRham.relations R B J δJ n).mkQ
    (DeRhamGlobalId.DeRhamGlobal.formMap f n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

theorem formMap_id (hf : DividedPowers.IsDPMorphism δI δI (𝟙 A : A ⟶ A).hom.toRingHom)
    (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δI n) : formMap (𝟙 A) hf n ω = ω := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δI n) ω
  rw [formMap_mk, DeRhamGlobalId.DeRhamGlobal.formMap_id]

theorem formMap_comp (f : A ⟶ B) (g : B ⟶ C)
    (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (hg : DividedPowers.IsDPMorphism δJ δL g.hom.toRingHom)
    (hfg : DividedPowers.IsDPMorphism δI δL (f ≫ g).hom.toRingHom)
    (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δI n) :
    formMap (f ≫ g) hfg n ω = formMap g hg n (formMap f hf n ω) := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δI n) ω
  rw [formMap_mk, formMap_mk, formMap_mk, DeRhamGlobalId.DeRhamGlobal.formMap_comp]

theorem formMap_differential (f : A ⟶ B)
    (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δI n) :
    formMap f hf (n + 1) (DeRham.PDDeRham.differential R A I δI n ω) =
      DeRham.PDDeRham.differential R B J δJ n (formMap f hf n ω) := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δI n) ω
  rw [DeRham.PDDeRham.differential_mk, formMap_mk, formMap_mk, DeRham.PDDeRham.differential_mk,
    DeRhamGlobalId.DeRhamGlobal.formMap_differential]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Ambient coordinate algebras of the crystalline objects. -/
def ambientAlgebras : (Cohomology.Site.Object p k X)ᵒᵖ ⥤ CommAlgCat.{u} (WittVector p k) where
  obj S := CommAlgCat.of (WittVector p k) S.unop.thickening.ring
  map f := CommAlgCat.ofHom f.unop.ambientMap
  map_id _ := rfl
  map_comp _ _ := rfl

def ordinaryFormsPresheaf (n : ℕ) :
    (Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} (WittVector p k) :=
  ambientAlgebras p k X ⋙ DeRhamGlobalId.DeRhamGlobal.formsFunctor n

def ordinaryDifferential (n : ℕ) :
    ordinaryFormsPresheaf p k X n ⟶ ordinaryFormsPresheaf p k X (n + 1) where
  app S := ModuleCat.ofHom (DeRhamPresentationTo.DeRhamPresentation.differential (WittVector p k) S.unop.thickening.ring n)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext (fun ω =>
    (DeRhamGlobalId.DeRhamGlobal.formMap_differential ((ambientAlgebras p k X).map f) n ω).symm))

theorem ordinaryDifferential_square (n : ℕ) :
    ordinaryDifferential p k X n ≫ ordinaryDifferential p k X (n + 1) = 0 := by
  apply NatTrans.ext
  funext S
  apply ModuleCat.hom_ext
  exact LinearMap.ext (DeRhamPresentationTo.DeRhamPresentation.differential_square _ _ n)

/-- Ordinary algebraic de Rham complexes evaluated on crystalline thickenings. -/
def ordinaryComplex :
    CochainComplex ((Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} (WittVector p k)) ℕ :=
  CochainComplex.of (ordinaryFormsPresheaf p k X) (ordinaryDifferential p k X)
    (ordinaryDifferential_square p k X)

/-- Divided-power forms on every affine crystalline object. -/
def formsPresheaf (n : ℕ) : (Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} (WittVector p k) where
  obj S := ModuleCat.of (WittVector p k)
    (DeRham.PDDeRham.Form (WittVector p k) S.unop.thickening.ring
      (RingHom.ker S.unop.thickening.reduction) S.unop.thickening.dividedPowers n)
  map f := ModuleCat.ofHom (formMap (CommAlgCat.ofHom f.unop.ambientMap) f.unop.dp_comp n)
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact formMap_id (A := CommAlgCat.of (WittVector p k) S.unop.thickening.ring)
      (δI := S.unop.thickening.dividedPowers) (𝟙 S).unop.dp_comp n ω
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact formMap_comp (CommAlgCat.ofHom f.unop.ambientMap)
      (CommAlgCat.ofHom g.unop.ambientMap) f.unop.dp_comp g.unop.dp_comp
      (f ≫ g).unop.dp_comp n ω

def differentialPresheaf (n : ℕ) : formsPresheaf p k X n ⟶ formsPresheaf p k X (n + 1) where
  app S := ModuleCat.ofHom (DeRham.PDDeRham.differential (WittVector p k) S.unop.thickening.ring
    (RingHom.ker S.unop.thickening.reduction) S.unop.thickening.dividedPowers n)
  naturality _ _ f := ModuleCat.hom_ext
    (LinearMap.ext (fun ω => (formMap_differential
      (CommAlgCat.ofHom f.unop.ambientMap) f.unop.dp_comp n ω).symm))

theorem differentialPresheaf_square (n : ℕ) :
    differentialPresheaf p k X n ≫ differentialPresheaf p k X (n + 1) = 0 := by
  apply NatTrans.ext
  funext S
  apply ModuleCat.hom_ext
  exact LinearMap.ext (DeRham.PDDeRham.differential_square _ _ _ _ n)

/-- The divided-power de Rham complex on the crystalline site before sheafification. -/
def presheafComplex : CochainComplex ((Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} (WittVector p k)) ℕ :=
  CochainComplex.of (formsPresheaf p k X) (differentialPresheaf p k X)
    (differentialPresheaf_square p k X)

/-- The divided-power quotient commutes with restriction between thickenings. -/
def quotientPresheaf (n : ℕ) : ordinaryFormsPresheaf p k X n ⟶ formsPresheaf p k X n where
  app S := ModuleCat.ofHom
    ((DeRham.PDDeRham.relations (WittVector p k) S.unop.thickening.ring
      (RingHom.ker S.unop.thickening.reduction) S.unop.thickening.dividedPowers n).mkQ.restrictScalars
        (WittVector p k))
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext (fun ω =>
    (formMap_mk (CommAlgCat.ofHom f.unop.ambientMap) f.unop.dp_comp n ω).symm))

/-- The natural morphism from ordinary to divided-power de Rham complexes
on the crystalline site. -/
def ordinaryToPD : ordinaryComplex p k X ⟶ presheafComplex p k X where
  f n := quotientPresheaf p k X n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    dsimp only [ordinaryComplex, presheafComplex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply NatTrans.ext
    funext S
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact DeRham.PDDeRham.differential_mk _ _ _ _ n ω

/-- Lift module universes and sheafify on the crystalline site. -/
def sheafificationFunctor :
    ((Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} (WittVector p k)) ⥤
      Sheaf (Cohomology.Site.topology p k X) (ModuleCat.{u + 1} (Cohomology.Site.CoefficientRing p k)) :=
  (Functor.whiskeringRight _ _ _).obj
    (ModuleCat.uliftFunctor.{u + 1} (WittVector p k) ⋙
      ModuleCat.restrictScalars
        (ULift.ringEquiv : Cohomology.Site.CoefficientRing p k ≃+* WittVector p k).toRingHom) ⋙
    presheafToSheaf (Cohomology.Site.topology p k X)
      (ModuleCat.{u + 1} (Cohomology.Site.CoefficientRing p k))

instance sheafification_preservesZero :
    (sheafificationFunctor p k X).PreservesZeroMorphisms := by
  dsimp [sheafificationFunctor]
  infer_instance

/-- The divided-power de Rham complex as sheaves on the crystalline site. -/
def sheafComplex :
    CochainComplex (Sheaf (Cohomology.Site.topology p k X)
      (ModuleCat.{u + 1} (Cohomology.Site.CoefficientRing p k))) ℕ :=
  ((sheafificationFunctor p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (presheafComplex p k X)

/-- The same quotient morphism after sheafification. -/
def ordinaryToPDSheaf :=
  ((sheafificationFunctor p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (ordinaryToPD p k X)

/-- In degree zero the divided-power forms are exactly ambient functions. -/
def degreeZeroPresheafIso : formsPresheaf p k X 0 ≅ Cohomology.Site.functions p k X :=
  NatIso.ofComponents
    (fun S => ((DeRham.PDDeRham.degreeZeroEquiv (WittVector p k) S.unop.thickening.ring
      (RingHom.ker S.unop.thickening.reduction) S.unop.thickening.dividedPowers).restrictScalars
        (WittVector p k)).toModuleIso)
    (fun {S T} f => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      have hω := DeRham.PDDeRham.symbol_degreeZeroEquiv (WittVector p k) S.unop.thickening.ring
        (RingHom.ker S.unop.thickening.reduction) S.unop.thickening.dividedPowers ω
      rw [← hω]
      change DeRham.PDDeRham.degreeZeroEquiv _ _ _ _
        (formMap (CommAlgCat.ofHom f.unop.ambientMap) f.unop.dp_comp 0
          (DeRham.PDDeRham.symbol _ _ _ _ _ _)) =
        f.unop.ambientMap (DeRham.PDDeRham.degreeZeroEquiv _ _ _ _ (DeRham.PDDeRham.symbol _ _ _ _ _ _))
      rw [formMap_symbol, DeRham.PDDeRham.degreeZeroEquiv_symbol, DeRham.PDDeRham.degreeZeroEquiv_symbol]
      rfl)

/-- The zeroth term of the global divided-power de Rham complex is the
crystalline structure sheaf used in the cohomology construction. -/
def degreeZeroSheafIso : (sheafComplex p k X).X 0 ≅ Cohomology.Site.structureSheaf p k X :=
  (sheafificationFunctor p k X).mapIso (degreeZeroPresheafIso p k X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal
