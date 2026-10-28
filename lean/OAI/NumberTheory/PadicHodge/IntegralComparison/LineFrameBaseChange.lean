import OAI.NumberTheory.PadicHodge.IntegralComparison.LineValuedKoszulPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameRefinement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent

/-! # Line Frame Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameBaseChange

noncomputable section

/-! Pulling an actual line frame through a commuting square pulls its
transition units through the same square. The comparison comes from
the native isomorphism of descent data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

theorem global_frame_transition {X U T : Scheme.{u}} (f : U ⟶ X)
    {L : X.Modules} (e : L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (p q : T ⟶ U) (h : p ≫ f = q ≫ f) :
    LineFrameCocycle.transition f
      ((Scheme.Modules.pullback f).mapIso e ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) p q h = 1 := by
  let t := (Scheme.Modules.pullback f).mapIso e ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f
  have hc := LineFrame.Comparison.correction_spec f t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) e
  have he : AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U)
      (LineFrame.Comparison.correction f t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) e).val = 𝟙 _ :=
    (cancel_epi t.hom).mp (hc.trans (Category.comp_id t.hom).symm)
  have hv : LineFrame.Comparison.correction f t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) e = 1 := by
    apply Units.ext
    change (LineFrame.Comparison.correction f t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) e).val = (1 : Γ(U, ⊤))
    simpa only [LineTrivializationCoboundary.scalar_value, AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar_id] using
      congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar he
  simpa only [LineFrameCocycle.transition_unit, hv, map_one, div_one] using
    LineFrameCocycle.comparison f t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) e p q h

theorem baseDatum_hom {X U T : Scheme.{u}} (f : U ⟶ X) (L : X.Modules)
    (base : T ⟶ X) (p q : T ⟶ U) (hp : p ≫ f = base) (hq : q ≫ f = base) :
    (AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f L).hom base
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
      (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q (hp.trans hq.symm)).hom.app L := by
  cases hq
  exact LineFrameCocycle.baseDatum_hom f L p q hp

variable {X Y U V T : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ Y)
  (a : V ⟶ U) (b : Y ⟶ X) (h : a ≫ f = g ≫ b) (L : X.Modules)

def sourceIso : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj L) ≅
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback f).obj L) :=
  AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks g
    (AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent.canonicalSquareIso f g a b h L).symm

theorem sourceIso_natural {M : X.Modules} (z : L ⟶ M) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map z) ≫
        (sourceIso f g a b h M).hom =
      (sourceIso f g a b h L).hom ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f).map z) := by
  let E := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => g) (p := b)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => a) (fun _ => h)
  have hz := E.inv.naturality z
  exact congrArg (fun w => w.hom PUnit.unit) hz

def comparison (p : T ⟶ V) :
    (Scheme.Modules.pullback p).obj
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj L)) ⟶
      (Scheme.Modules.pullback (p ≫ a)).obj ((Scheme.Modules.pullback f).obj L) :=
  (Scheme.Modules.pullback p).map (sourceIso f g a b h L).hom ≫
    (Scheme.Modules.pullbackComp p a).hom.app ((Scheme.Modules.pullback f).obj L)

include h in
theorem square_condition (p q : T ⟶ V) (hpq : p ≫ g = q ≫ g) :
    (p ≫ a) ≫ f = (q ≫ a) ≫ f := by
  simpa only [Category.assoc, h] using congrArg (fun z => z ≫ b) hpq

private theorem gluingDatum (p q : T ⟶ V) (hpq : p ≫ g = q ≫ g) :
    (Scheme.Modules.pullback p).map (sourceIso f g a b h L).hom ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f g a b h
          (AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f L)).hom (q ≫ g)
            (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hpq rfl =
      (AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum g ((Scheme.Modules.pullback b).obj L)).hom
          (q ≫ g) (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hpq rfl ≫
        (Scheme.Modules.pullback q).map (sourceIso f g a b h L).hom := by
  let d := (AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent.canonicalSquareIso f g a b h L).symm
  exact d.hom.comm (q ≫ g) (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hpq rfl

private theorem gluing_of_comm {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ D₁ D₂ : C}
    (a : A₁ ⟶ B₁) (b : A₂ ⟶ B₂) (f : A₁ ⟶ A₂) (g : D₁ ⟶ D₂)
    (e₁ : B₁ ≅ D₁) (e₂ : B₂ ≅ D₂)
    (h : a ≫ (e₁.hom ≫ g ≫ e₂.inv) = f ≫ b) :
    f ≫ (b ≫ e₂.hom) = (a ≫ e₁.hom) ≫ g := by
  have h' := congrArg (fun z => z ≫ e₂.hom) h
  simpa only [Category.assoc, e₂.inv_hom_id, Category.comp_id] using h'.symm

theorem gluing (p q : T ⟶ V) (hpq : p ≫ g = q ≫ g) :
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing g p q hpq).hom.app ((Scheme.Modules.pullback b).obj L) ≫
        comparison f g a b h L q =
      comparison f g a b h L p ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (p ≫ a) (q ≫ a)
          (square_condition f g a b h p q hpq)).hom.app L := by
  have hd := gluingDatum f g a b h L p q hpq
  rw [AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing.pulledHom, baseDatum_hom, baseDatum_hom] at hd
  change (Scheme.Modules.pullback p).map (sourceIso f g a b h L).hom ≫
      ((Scheme.Modules.pullbackComp p a).hom.app ((Scheme.Modules.pullback f).obj L) ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (p ≫ a) (q ≫ a) (square_condition f g a b h p q hpq)).hom.app L ≫
          (Scheme.Modules.pullbackComp q a).inv.app ((Scheme.Modules.pullback f).obj L)) =
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing g p q hpq).hom.app ((Scheme.Modules.pullback b).obj L) ≫
      (Scheme.Modules.pullback q).map (sourceIso f g a b h L).hom at hd
  exact gluing_of_comm
    ((Scheme.Modules.pullback p).map (sourceIso f g a b h L).hom)
    ((Scheme.Modules.pullback q).map (sourceIso f g a b h L).hom)
    ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing g p q hpq).hom.app ((Scheme.Modules.pullback b).obj L))
    ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (p ≫ a) (q ≫ a) (square_condition f g a b h p q hpq)).hom.app L)
    ((Scheme.Modules.pullbackComp p a).app ((Scheme.Modules.pullback f).obj L))
    ((Scheme.Modules.pullbackComp q a).app ((Scheme.Modules.pullback f).obj L)) hd

variable {L} (t : (Scheme.Modules.pullback f).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U)

def frame : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj L) ≅
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V :=
  sourceIso f g a b h L ≪≫ LineFrame.Comparison.frameAt f t a

theorem frame_at (p : T ⟶ V) :
    (LineFrame.Comparison.frameAt g (frame f g a b h t) p).hom =
      comparison f g a b h L p ≫ (LineFrame.Comparison.frameAt f t (p ≫ a)).hom := by
  change (Scheme.Modules.pullback p).map
      ((sourceIso f g a b h L).hom ≫ (LineFrame.Comparison.frameAt f t a).hom) ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom = _
  rw [Functor.map_comp, Category.assoc, LineFrameCocycle.frame_pullback]
  exact (Category.assoc _ _ _).symm

theorem transition (p q : T ⟶ V) (hpq : p ≫ g = q ≫ g) :
    LineFrameCocycle.transition g (frame f g a b h t) p q hpq =
      LineFrameCocycle.transition f t (p ≫ a) (q ≫ a)
        (square_condition f g a b h p q hpq) := by
  apply congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso
  apply Iso.ext
  apply (cancel_epi (LineFrame.Comparison.frameAt g (frame f g a b h t) p).hom).mp
  simp only [LineFrameCocycle.transitionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  rw [frame_at, frame_at]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (LineFrame.Comparison.frameAt f t (q ≫ a)).hom)
      (gluing f g a b h L p q hpq)).trans (Category.assoc _ _ _))

/-- Restriction to a new relation scheme agrees with the transition
of the pulled frame, including for a closed base change. -/
theorem transition_square {T₀ : Scheme.{u}}
    (p q : T ⟶ U) (hpq : p ≫ f = q ≫ f)
    (p₀ q₀ : T₀ ⟶ V) (hpq₀ : p₀ ≫ g = q₀ ≫ g) (r : T₀ ⟶ T)
    (hp : r ≫ p = p₀ ≫ a) (hq : r ≫ q = q₀ ≫ a) :
    Units.map r.appTop.hom.toMonoidHom (LineFrameCocycle.transition f t p q hpq) =
      LineFrameCocycle.transition g (frame f g a b h t) p₀ q₀ hpq₀ := by
  rw [LineFrameCocycle.transition_restrict]
  simpa only [hp, hq] using (transition f g a b h t p₀ q₀ hpq₀).symm

theorem transition_one_of_reduced_frame {T₀ : Scheme.{u}}
    (p q : T ⟶ U) (hpq : p ≫ f = q ≫ f)
    (p₀ q₀ : T₀ ⟶ V) (hpq₀ : p₀ ≫ g = q₀ ≫ g) (r : T₀ ⟶ T)
    (hp : r ≫ p = p₀ ≫ a) (hq : r ≫ q = q₀ ≫ a)
    (e : (Scheme.Modules.pullback b).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    (ht : frame f g a b h t =
      (Scheme.Modules.pullback g).mapIso e ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g) :
    Units.map r.appTop.hom.toMonoidHom (LineFrameCocycle.transition f t p q hpq) = 1 := by
  rw [transition_square f g a b h t p q hpq p₀ q₀ hpq₀ r hp hq, ht]
  exact global_frame_transition g e p₀ q₀ hpq₀

/-- The correction comparing two frames restricts by the actual map
on global units, including along a closed thickening. -/
theorem correction {M : X.Modules}
    (s : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U) (e : L ≅ M) :
    LineFrame.Comparison.correction g (frame f g a b h t) (frame f g a b h s)
        ((Scheme.Modules.pullback b).mapIso e) =
      Units.map a.appTop.hom.toMonoidHom (LineFrame.Comparison.correction f t s e) := by
  let t' := frame f g a b h t
  let s' := frame f g a b h s
  let e' := (Scheme.Modules.pullback b).mapIso e
  let v := LineFrame.Comparison.correction f t s e
  have hn : t'.hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V) (a.appTop v.val) =
      (Scheme.Modules.pullback g).map e'.hom ≫ s'.hom := by
    change ((sourceIso f g a b h L).hom ≫ (LineFrame.Comparison.frameAt f t a).hom) ≫ _ =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map e.hom) ≫
        ((sourceIso f g a b h M).hom ≫ (LineFrame.Comparison.frameAt f s a).hom)
    rw [Category.assoc, ← LineFrame.Comparison.correction_at f t s e a,
      ← Category.assoc, ← sourceIso_natural f g a b h L e.hom, Category.assoc]
  have hc := LineFrame.Comparison.correction_spec g t' s' e'
  have heq := (cancel_epi t'.hom).mp (hc.trans hn.symm)
  apply Units.ext
  change (LineFrame.Comparison.correction g t' s' e').val = a.appTop v.val
  simpa only [LineTrivializationCoboundary.scalar_value] using
    congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar heq

open scoped TensorProduct

/-- The map on residue coefficients, viewed over the original scalar rings. -/
private def quotientScalarMap (R S : Type u) [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap φ) :
    (R ⧸ I) →ₛₗ[φ] (S ⧸ J) where
  toFun := Ideal.quotientMap J φ hIJ
  map_add' := (Ideal.quotientMap J φ hIJ).map_add
  map_smul' r x := by
    change (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk I r * x) =
      Ideal.Quotient.mk J (φ r) * (Ideal.quotientMap J φ hIJ) x
    rw [map_mul, Ideal.quotientMap_mk]

/-- Restrict a line together with its quotient coefficients. -/
def lineMap (R S : Type u) [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap φ)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (f : M →ₛₗ[φ] N) :
    ((R ⧸ I) ⊗[R] M) →ₛₗ[φ] ((S ⧸ J) ⊗[S] N) :=
  TensorProduct.map (quotientScalarMap R S φ I J hIJ) f

theorem lineMap_tmul (R S : Type u) [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap φ)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (f : M →ₛₗ[φ] N)
    (a : R ⧸ I) (x : M) :
    lineMap R S φ I J hIJ M N f (a ⊗ₜ[R] x) =
      Ideal.quotientMap J φ hIJ a ⊗ₜ[S] f x :=
  TensorProduct.map_tmul _ _ _ _

theorem lineFrame_symm_tmul (R : Type u) [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) (e : M ≅ ModuleCat.of R R) (a : R ⧸ I) :
    (LineValuedKoszulPurity.lineFrame R I M e).symm a = a ⊗ₜ[R] e.inv 1 := by
  apply (LineValuedKoszulPurity.lineFrame R I M e).injective
  rw [LinearEquiv.apply_symm_apply, LineValuedKoszulPurity.lineFrame_tmul]
  have he : e.hom (e.inv 1) = 1 := ConcreteCategory.congr_hom e.inv_hom_id 1
  rw [he, map_one, mul_one]

theorem lineFrame_symm_map (R S : Type u) [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap φ)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (f : M →ₛₗ[φ] N)
    (eR : M ≅ ModuleCat.of R R) (eS : N ≅ ModuleCat.of S S)
    (he : ∀ x, eS.hom (f x) = φ (eR.hom x)) (a : R ⧸ I) :
    lineMap R S φ I J hIJ M N f ((LineValuedKoszulPurity.lineFrame R I M eR).symm a) =
      (LineValuedKoszulPurity.lineFrame S J N eS).symm (Ideal.quotientMap J φ hIJ a) := by
  rw [lineFrame_symm_tmul, lineMap_tmul, lineFrame_symm_tmul]
  apply congrArg (fun x : N => Ideal.quotientMap J φ hIJ a ⊗ₜ[S] x)
  apply eS.toLinearEquiv.injective
  change eS.hom (f (eR.inv 1)) = eS.hom (eS.inv 1)
  have hR : eR.hom (eR.inv 1) = 1 := ConcreteCategory.congr_hom eR.inv_hom_id 1
  have hS : eS.hom (eS.inv 1) = 1 := ConcreteCategory.congr_hom eS.inv_hom_id 1
  rw [he, hR, hS, map_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameBaseChange
