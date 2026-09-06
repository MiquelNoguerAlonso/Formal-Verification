import MoreRules

/-!
  ClauseComplete.lean -- clause-traceability specification layer for the dated
  regulatory corpus used by the paper.  This module separates three claims:

  * a clause is represented by a typed field or constructor;
  * compliance of a supplied record is executable and decidable; and
  * mathematical consequences of the model are proved.

  The module does not assert that an exchange's production system supplies a
  truthful record.  It turns previously implicit exceptions and procedural
  duties into explicit inputs that a certification exercise must discharge.
-/

namespace Rule737

/-! ## Shared vocabulary -/

inductive ClauseKind where
  | definition | numeric | stateTransition | exception | procedure | disclosure
  deriving DecidableEq, Repr

inductive CorpusRule where
  | sec600 | sec605 | sec610 | sec611 | sec612 | regSho201 | luld
  | nyse731 | nyse735 | nyse737
  | nasdaq4702 | nasdaq4703 | nasdaq4752 | nasdaq4753 | nasdaq4754 | nasdaq4757
  deriving DecidableEq, Repr

/-- A ledger destination contains an actual Lean value, function, projection,
    or tuple of them.  A misspelled or deleted destination therefore fails to
    elaborate instead of surviving as an unchecked string. -/
structure FormalDestination where
  name : String
  α : Type
  object : α

def destination {α : Type} (name : String) (object : α) : FormalDestination :=
  ⟨name, α, object⟩

structure ClauseSpec where
  rule : CorpusRule
  citation : String
  kind : ClauseKind
  destination : FormalDestination

/-- Exemptive relief can replace the ordinary checklist only when it has been
    granted, covers every duty checked by that record, and all stated
    conditions are satisfied.  Partial relief belongs at the affected field,
    not in this whole-record alternative. -/
structure ExemptionAttestation where
  granted : Bool
  coversAllCheckedDuties : Bool
  conditionsSatisfied : Bool
  deriving Repr

def validExemptionAttestation (e : ExemptionAttestation) : Bool :=
  e.granted && e.coversAllCheckedDuties && e.conditionsSatisfied

theorem validExemptionAttestation_iff (e : ExemptionAttestation) :
    validExemptionAttestation e = true ↔
      e.granted = true ∧ e.coversAllCheckedDuties = true ∧
        e.conditionsSatisfied = true := by
  simp [validExemptionAttestation, and_assoc]

theorem bool_true_or_false (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-! ## Regulation NMS Rule 600 definitions used by this corpus -/

/-- Numerical round-lot kernel, with prices in $0.0001 units.  For an existing
    stock, the inspected input must be a primary-exchange-supplied average
    normalized to cents; `checkedRoundLotSize600` enforces that interface.
    Calculation/normalization and the evaluation/operative period require
    external evidence.  No rounding policy for raw averages is invented here. -/
def roundLotSize600 (averageClosingPrice : Nat) (newNmsStock : Bool) : Nat :=
  if newNmsStock then 100
  else if averageClosingPrice ≤ 250 * dollar then 100
  else if averageClosingPrice ≤ 1000 * dollar then 40
  else if averageClosingPrice ≤ 10000 * dollar then 10
  else 1

theorem roundLotSize600_new_stock (p : Nat) : roundLotSize600 p true = 100 := by
  simp [roundLotSize600]

theorem roundLotSize600_low (p : Nat) (h : p ≤ 250 * dollar) :
    roundLotSize600 p false = 100 := by
  simp [roundLotSize600, h]

theorem roundLotSize600_middle40 (p : Nat)
    (hlo : 250 * dollar < p) (hhi : p ≤ 1000 * dollar) :
    roundLotSize600 p false = 40 := by
  simp [roundLotSize600, Nat.not_le.mpr hlo, hhi]

theorem roundLotSize600_middle10 (p : Nat)
    (hlo : 1000 * dollar < p) (hhi : p ≤ 10000 * dollar) :
    roundLotSize600 p false = 10 := by
  have h250 : 250 * dollar < p := by omega
  simp [roundLotSize600, Nat.not_le.mpr h250, Nat.not_le.mpr hlo, hhi]

theorem roundLotSize600_high (p : Nat) (h : 10000 * dollar < p) :
    roundLotSize600 p false = 1 := by
  simp [roundLotSize600, Nat.not_le.mpr (by omega : 250 * dollar < p),
    Nat.not_le.mpr (by omega : 1000 * dollar < p), Nat.not_le.mpr h]

/-- Inspected round-lot boundary: existing-stock averages off the cent grid
    are rejected instead of silently assigned a tier.  New stocks need no
    historical average. -/
def checkedRoundLotSize600 (p : Nat) (newNmsStock : Bool) : Option Nat :=
  if newNmsStock then some 100
  else if p % 100 = 0 then some (roundLotSize600 p false) else none

theorem checkedRoundLotSize600_new_stock (p : Nat) :
    checkedRoundLotSize600 p true = some 100 := by simp [checkedRoundLotSize600]

theorem checkedRoundLotSize600_on_grid (p : Nat) (h : p % 100 = 0) :
    checkedRoundLotSize600 p false = some (roundLotSize600 p false) := by
  simp [checkedRoundLotSize600, h]

theorem checkedRoundLotSize600_off_grid (p : Nat) (h : p % 100 ≠ 0) :
    checkedRoundLotSize600 p false = none := by simp [checkedRoundLotSize600, h]

theorem checkedRoundLotSize600_boundaries :
    checkedRoundLotSize600 2500000 false = some 100 ∧
    checkedRoundLotSize600 2500001 false = none ∧
    checkedRoundLotSize600 2500100 false = some 40 ∧
    checkedRoundLotSize600 10000100 false = some 10 ∧
    checkedRoundLotSize600 100000100 false = some 1 := by decide

/-- Rule 600(b)(89)(i)(F) is the applicable minimum-pricing-increment indicator,
    not odd-lot information (600(b)(69)).  SEC Release 34-101070, p. 513;
    June 2026 relief: Release 34-105656, pp. 5-6 and 8. -/
inductive MinimumIncrementIndicatorProfile600 where
  | june2026Relief | amendedOperative
  deriving DecidableEq, Repr

def september2026MinimumIncrementIndicatorProfile600 : MinimumIncrementIndicatorProfile600 :=
  .june2026Relief

theorem minimumIncrementIndicator_amended_not_september2026 :
    MinimumIncrementIndicatorProfile600.amendedOperative ≠
      september2026MinimumIncrementIndicatorProfile600 := by
  decide

/-! ## Regulation NMS Rule 610 -/

/-- The dated parameter profile distinguishes the legacy cap used during the
    Commission's temporary relief from the lower cap in the amended text.
    Prices and fees use $0.0001 units. -/
inductive FeeProfile610 where
  | legacyRelief2026 | amendedAfterRelief
  deriving DecidableEq, Repr

def september2026FeeProfile610 : FeeProfile610 := .legacyRelief2026

/-- Under the legacy profile the cap is $0.003 at or above $1 and 0.3% below
    $1.  Under the amended profile it is $0.001 and 0.1%, respectively. -/
def accessFeeCap610 (profile : FeeProfile610) (quotePrice : Nat) : Nat :=
  match profile with
  | .legacyRelief2026 =>
      if dollar ≤ quotePrice then 30 else (3 * quotePrice) / 1000
  | .amendedAfterRelief =>
      if dollar ≤ quotePrice then 10 else quotePrice / 1000

structure Rule610State where
  feeProfile : FeeProfile610
  fairSroTradingAccess : Bool
  equivalentDisplayOnlyAccess : Bool
  fairDisplayOnlyAccess : Bool
  quotePrice : Nat
  accessFee : Nat
  feeKnownAtExecution : Bool
  avoidsProtectedLocks : Bool
  avoidsManualLocks : Bool
  reconcilesLocks : Bool
  noLockPattern : Bool
  commissionExemption : ExemptionAttestation
  deriving Repr

/-- Generic checklist under the profile carried by the record. -/
def rule610ChecklistPasses (s : Rule610State) : Bool :=
  validExemptionAttestation s.commissionExemption ||
    (s.fairSroTradingAccess && s.equivalentDisplayOnlyAccess &&
     s.fairDisplayOnlyAccess &&
     decide (s.accessFee ≤ accessFeeCap610 s.feeProfile s.quotePrice) &&
     s.feeKnownAtExecution && s.avoidsProtectedLocks && s.avoidsManualLocks &&
     s.reconcilesLocks && s.noLockPattern)

/-- Dated September 5, 2026 verification: the lower amended fee caps were subject
    to temporary exemptive relief, so the legacy profile must be selected. -/
def rule610Complies (s : Rule610State) : Bool :=
  decide (s.feeProfile = september2026FeeProfile610) &&
    rule610ChecklistPasses s

theorem accessFeeCap610_legacy_at_or_above_dollar (p : Nat) (h : dollar ≤ p) :
    accessFeeCap610 .legacyRelief2026 p = 30 := by
  simp [accessFeeCap610, h]

/-- The analytic kernel's legacy dollar-price constant is exactly the dated
    clause layer's legacy-relief dollar-price branch. -/
theorem feeCap_eq_accessFeeCap610_legacy_dollar (p : Nat) (h : dollar ≤ p) :
    feeCap = accessFeeCap610 .legacyRelief2026 p := by
  rw [accessFeeCap610_legacy_at_or_above_dollar p h]
  rfl

theorem accessFeeCap610_legacy_below_dollar (p : Nat) (h : p < dollar) :
    accessFeeCap610 .legacyRelief2026 p = (3 * p) / 1000 := by
  simp [accessFeeCap610, Nat.not_le.mpr h]

theorem accessFeeCap610_amended_at_or_above_dollar (p : Nat) (h : dollar ≤ p) :
    accessFeeCap610 .amendedAfterRelief p = 10 := by
  simp [accessFeeCap610, h]

theorem accessFeeCap610_amended_below_dollar (p : Nat) (h : p < dollar) :
    accessFeeCap610 .amendedAfterRelief p = p / 1000 := by
  simp [accessFeeCap610, Nat.not_le.mpr h]

theorem rule610_exemption (s : Rule610State)
    (hp : s.feeProfile = september2026FeeProfile610)
    (he : validExemptionAttestation s.commissionExemption = true) :
    rule610Complies s = true := by
  simp [rule610Complies, rule610ChecklistPasses, hp, he]

theorem rule610_amended_profile_not_september2026 (s : Rule610State)
    (h : s.feeProfile = .amendedAfterRelief) :
    rule610Complies s = false := by
  simp [rule610Complies, september2026FeeProfile610, h]

/-! ## Regulation NMS Rule 611 -/

inductive Rule611Exception where
  | systemFailure
  | notRegularWay
  | singlePriceAuction
  | crossedProtectedMarket
  | incomingISO
  | outboundISO
  | benchmarkTrade
  | flickeringQuote
  | stoppedOrder
  deriving DecidableEq, Repr

structure Rule611ExceptionFacts where
  systemFailure : Bool
  notRegularWay : Bool
  singlePriceAuction : Bool
  crossedProtectedMarket : Bool
  incomingISO : Bool
  outboundISOSweptFullDisplayedSize : Bool
  benchmarkTermsNotDeterminable : Bool
  inferiorQuoteWithinOneSecond : Bool
  stoppedCustomer : Bool
  stoppedCustomerAgreed : Bool
  stoppedPriceCondition : Bool
  deriving Repr

def validRule611Exception (f : Rule611ExceptionFacts) : Rule611Exception → Bool
  | .systemFailure => f.systemFailure
  | .notRegularWay => f.notRegularWay
  | .singlePriceAuction => f.singlePriceAuction
  | .crossedProtectedMarket => f.crossedProtectedMarket
  | .incomingISO => f.incomingISO
  | .outboundISO => f.outboundISOSweptFullDisplayedSize
  | .benchmarkTrade => f.benchmarkTermsNotDeterminable
  | .flickeringQuote => f.inferiorQuoteWithinOneSecond
  | .stoppedOrder =>
      f.stoppedCustomer && f.stoppedCustomerAgreed && f.stoppedPriceCondition

structure Rule611State where
  writtenPolicies : Bool
  regularSurveillance : Bool
  promptRemediation : Bool
  tradeThrough : Bool
  claimedException : Option Rule611Exception
  exceptionFacts : Rule611ExceptionFacts
  routedISO : Bool
  reasonableISOSteps : Bool
  commissionExemption : ExemptionAttestation
  deriving Repr

def rule611TransactionAllowed (s : Rule611State) : Bool :=
  !s.tradeThrough ||
    match s.claimedException with
    | none => false
    | some e => validRule611Exception s.exceptionFacts e

def rule611Complies (s : Rule611State) : Bool :=
  validExemptionAttestation s.commissionExemption ||
    (s.writtenPolicies && s.regularSurveillance && s.promptRemediation &&
     rule611TransactionAllowed s && (!s.routedISO || s.reasonableISOSteps))

theorem rule611_no_trade_through_allowed (s : Rule611State)
    (h : s.tradeThrough = false) : rule611TransactionAllowed s = true := by
  simp [rule611TransactionAllowed, h]

theorem rule611_all_exceptions_decidable (e : Rule611Exception)
    (f : Rule611ExceptionFacts) :
    validRule611Exception f e = true ∨ validRule611Exception f e = false := by
  exact bool_true_or_false (validRule611Exception f e)

/-! ## Regulation NMS Rule 612 -/

/-- The amended text is codified, but compliance was temporarily relieved to
    the first business day of November 2027. -/
inductive PricingProfile612 where
  | legacyRelief2026 | amendedAfterRelief
  deriving DecidableEq, Repr

def september2026PricingProfile612 : PricingProfile612 := .legacyRelief2026

inductive EvaluationPeriod612 where
  | januaryThroughMarch | julyThroughSeptember
  deriving DecidableEq, Repr

inductive OperativePeriod612 where
  | mayThroughOctober | novemberThroughApril
  deriving DecidableEq, Repr

def operativePeriodFor612 : EvaluationPeriod612 → OperativePeriod612
  | .januaryThroughMarch => .mayThroughOctober
  | .julyThroughSeptember => .novemberThroughApril

theorem operativePeriodFor612_january_through_march :
    operativePeriodFor612 .januaryThroughMarch = .mayThroughOctober := rfl

theorem operativePeriodFor612_july_through_september :
    operativePeriodFor612 .julyThroughSeptember = .novemberThroughApril := rfl

/-- Minimum increment in $0.0001 units.  `twaSpread` uses the same units;
    150 denotes $0.015 and 50 denotes $0.005. -/
def minimumTick612 (profile : PricingProfile612) (twaSpread price : Nat)
    (newNmsStock : Bool) : Nat :=
  if price < dollar then 1
  else match profile with
    | .legacyRelief2026 => 100
    | .amendedAfterRelief =>
        if newNmsStock then 100 else if twaSpread ≤ 150 then 50 else 100

def rule612PriceComplies (profile : PricingProfile612) (twaSpread price : Nat)
    (newNmsStock : Bool) : Bool :=
  price % minimumTick612 profile twaSpread price newNmsStock = 0

structure Rule612State where
  pricingProfile : PricingProfile612
  evaluationPeriod : EvaluationPeriod612
  operativePeriod : OperativePeriod612
  primaryListingExchangeMeasuredSpread : Bool
  twaSpread : Nat
  price : Nat
  newNmsStock : Bool
  displayedPricesComply : Bool
  rankedPricesComply : Bool
  acceptedPricesComply : Bool
  indicationsOfInterestComply : Bool
  commissionExemption : ExemptionAttestation
  deriving Repr

def rule612SchedulePasses (s : Rule612State) : Bool :=
  match s.pricingProfile with
  | .legacyRelief2026 => true
  | .amendedAfterRelief =>
      s.primaryListingExchangeMeasuredSpread &&
        decide (s.operativePeriod = operativePeriodFor612 s.evaluationPeriod)

def rule612ChecklistPasses (s : Rule612State) : Bool :=
  validExemptionAttestation s.commissionExemption ||
    (rule612SchedulePasses s &&
     rule612PriceComplies s.pricingProfile s.twaSpread s.price s.newNmsStock &&
     s.displayedPricesComply && s.rankedPricesComply &&
     s.acceptedPricesComply && s.indicationsOfInterestComply)

def rule612Complies (s : Rule612State) : Bool :=
  decide (s.pricingProfile = september2026PricingProfile612) &&
    rule612ChecklistPasses s

theorem rule612_amended_profile_not_september2026 (s : Rule612State)
    (h : s.pricingProfile = .amendedAfterRelief) :
    rule612Complies s = false := by
  simp [rule612Complies, september2026PricingProfile612, h]

theorem minimumTick612_legacy_subdollar (s p : Nat) (h : p < dollar)
    (n : Bool) : minimumTick612 .legacyRelief2026 s p n = 1 := by
  simp [minimumTick612, h]

theorem minimumTick612_legacy_at_or_above_dollar (s p : Nat)
    (h : dollar ≤ p) (n : Bool) :
    minimumTick612 .legacyRelief2026 s p n = 100 := by
  simp [minimumTick612, Nat.not_lt.mpr h]

/-- The analytic Rule 612 predicate is exactly price compliance under the
    dated legacy-relief profile.  Below one dollar the $0.0001 grid is
    automatic in the paper's integer price units; at or above one dollar both
    objects require a whole-cent multiple. -/
theorem rule612_iff_minimumTick612_legacy (s p : Nat) (n : Bool) :
    rule612 p ↔ rule612PriceComplies .legacyRelief2026 s p n = true := by
  unfold rule612 rule612PriceComplies
  by_cases hp : p < dollar
  · have hn : ¬ dollar ≤ p := Nat.not_le.mpr hp
    have hm : p % 1 = 0 := Nat.mod_one p
    simp [minimumTick612, hp, hn, hm]
  · have hd : dollar ≤ p := Nat.le_of_not_gt hp
    simp [minimumTick612, hp, hd, penny]

theorem minimumTick612_amended_subdollar (s p : Nat) (h : p < dollar)
    (n : Bool) : minimumTick612 .amendedAfterRelief s p n = 1 := by
  simp [minimumTick612, h]

theorem minimumTick612_amended_new_stock (s p : Nat) (h : dollar ≤ p) :
    minimumTick612 .amendedAfterRelief s p true = 100 := by
  simp [minimumTick612, Nat.not_lt.mpr h]

theorem minimumTick612_amended_narrow (s p : Nat) (hp : dollar ≤ p)
    (hs : s ≤ 150) : minimumTick612 .amendedAfterRelief s p false = 50 := by
  simp [minimumTick612, Nat.not_lt.mpr hp, hs]

theorem minimumTick612_amended_wide (s p : Nat) (hp : dollar ≤ p)
    (hs : 150 < s) : minimumTick612 .amendedAfterRelief s p false = 100 := by
  simp [minimumTick612, Nat.not_lt.mpr hp, Nat.not_le.mpr hs]

/-! ## Regulation SHO Rule 201 -/

def tenPercentDecline201 (priorClose currentPrice : Nat) : Bool :=
  decide (10 * currentPrice ≤ 9 * priorClose)

inductive ShortExemptReason201 where
  | aboveNbbAtSubmission
  | ownerDeliveryRestriction
  | oddLotMarketMaker
  | convertibleArbitrage
  | foreignArbitrage
  | underwriterOverallotment
  | underwriterLayoff
  | risklessPrincipal
  | vwap
  deriving DecidableEq, Repr

structure ShortExemptFacts201 where
  aboveNbbAtSubmission : Bool
  markingPolicies : Bool
  markingSurveillance : Bool
  markingRemediation : Bool
  ownerAndPromptDelivery : Bool
  oddLotWithinUnit : Bool
  convertibleGoodFaith : Bool
  foreignImmediateCover : Bool
  underwriterOverallotment : Bool
  underwriterLayoff : Bool
  customerOrderFirst : Bool
  allocationWithin60Seconds : Bool
  timeSequencedRecords : Bool
  vwapEveryRegularWayTrade : Bool
  vwapAggregateAndDivide : Bool
  vwapModifier : Bool
  activeSecurityOrTwentyNameBasket : Bool
  noManipulativePurpose : Bool
  principalPositionWithinTenPercentAdtv : Bool
  deriving Repr

def validShortExempt201 (f : ShortExemptFacts201) : ShortExemptReason201 → Bool
  | .aboveNbbAtSubmission =>
      f.aboveNbbAtSubmission && f.markingPolicies && f.markingSurveillance &&
        f.markingRemediation
  | .ownerDeliveryRestriction => f.ownerAndPromptDelivery
  | .oddLotMarketMaker => f.oddLotWithinUnit
  | .convertibleArbitrage => f.convertibleGoodFaith
  | .foreignArbitrage => f.foreignImmediateCover
  | .underwriterOverallotment => f.underwriterOverallotment
  | .underwriterLayoff => f.underwriterLayoff
  | .risklessPrincipal =>
      f.customerOrderFirst && f.allocationWithin60Seconds && f.timeSequencedRecords
  | .vwap =>
      f.vwapEveryRegularWayTrade && f.vwapAggregateAndDivide && f.vwapModifier &&
      f.activeSecurityOrTwentyNameBasket && f.noManipulativePurpose &&
      f.principalPositionWithinTenPercentAdtv

structure Rule201State where
  coveredSecurity : Bool
  priorClose : Nat
  currentPrice : Nat
  listingMarketDetermined : Bool
  listingMarketNotified : Bool
  restrictionDay : Nat
  nbbContinuouslyAvailable : Bool
  shortSale : Bool
  executionPrice : Nat
  currentNbb : Nat
  initiallyDisplayedAboveNbb : Bool
  markedShortExempt : Bool
  exemptReason : Option ShortExemptReason201
  exemptFacts : ShortExemptFacts201
  tradingCenterPolicies : Bool
  tradingCenterSurveillance : Bool
  promptRemediation : Bool
  sroRuleConforming : Bool
  commissionExemption : ExemptionAttestation
  deriving Repr

def restrictionApplies201 (s : Rule201State) : Bool :=
  s.coveredSecurity && tenPercentDecline201 s.priorClose s.currentPrice &&
    s.listingMarketDetermined && s.listingMarketNotified &&
    decide (s.restrictionDay ≤ 1) && s.nbbContinuouslyAvailable

def transactionAllowed201 (s : Rule201State) : Bool :=
  !restrictionApplies201 s || !s.shortSale || decide (s.currentNbb < s.executionPrice) ||
    s.initiallyDisplayedAboveNbb ||
    (s.markedShortExempt &&
      match s.exemptReason with
      | none => false
      | some r => validShortExempt201 s.exemptFacts r)

def rule201Complies (s : Rule201State) : Bool :=
  validExemptionAttestation s.commissionExemption ||
    (s.tradingCenterPolicies && s.tradingCenterSurveillance && s.promptRemediation &&
     s.sroRuleConforming && transactionAllowed201 s)

theorem tenPercentDecline201_iff (prior current : Nat) :
    tenPercentDecline201 prior current = true ↔ 10 * current ≤ 9 * prior := by
  simp [tenPercentDecline201]

theorem rule201_long_sale_allowed (s : Rule201State) (h : s.shortSale = false) :
    transactionAllowed201 s = true := by
  simp [transactionAllowed201, h]

theorem all_short_exempt_reasons_decidable (r : ShortExemptReason201)
    (f : ShortExemptFacts201) :
    validShortExempt201 f r = true ∨ validShortExempt201 f r = false := by
  exact bool_true_or_false (validShortExempt201 f r)

/-! ## Rule 605: amended disclosure schema with the September 2026 profile -/

/-- The amended rule was generally in compliance from August 1, 2026, while
    statistics relative to the best available displayed price had a separate
    November 1, 2026 compliance date. -/
inductive Rule605Profile where
  | augustThroughOctober2026
  | november2026AndLater
  deriving DecidableEq, Repr

def september2026Rule605Profile : Rule605Profile :=
  .augustThroughOctober2026

inductive OrderType605 where
  | market | marketableLimit | marketableIOC | midpointBetter
  | midpointBetterIOC | executableNonmarketable | executableNonmarketableIOC
  | executableStopMarket | executableStopMarketableLimit
  | executableStopNonmarketableLimit
  deriving DecidableEq, Repr

inductive CoreField605 where
  | orderCount | notional | shares | cancelled | localExecution | awayExecution
  | speedLt100us | speed100us1ms | speed1ms10ms | speed10ms1s
  | speed1s10s | speed10s30s | speed30s5m | speedGe5m
  | realized50ms | pctRealized50ms | realized1s | pctRealized1s
  | realized15s | pctRealized15s | realized1m | pctRealized1m
  | realized5m | pctRealized5m | midpoint
  deriving DecidableEq, Repr

inductive ImmediateField605 where
  | quotedSpread | effectiveSpread | pctEffectiveSpread | effectiveOverQuoted
  | improvedShares | improvementAmount | improvementTime | atQuoteShares
  | atQuoteTime | outsideQuoteShares | outsideQuoteAmount | outsideQuoteTime
  | betterDisplayedShares | betterDisplayedAmount | atBestDisplayedShares
  | outsideBestDisplayedShares | outsideBestDisplayedAmount
  | orderSizeBenchmark | benchmarkExcess
  deriving DecidableEq, Repr

inductive NonmarketableField605 where
  | filledOrders | executableMarketShares | executableExchangeShares | executionTime
  deriving DecidableEq, Repr

inductive SummaryField605 where
  | averageShares | averageNotional | midpoint | pctQuoteOrBetter
  | pctImproved | weightedPctImprovement | pctEffectiveSpread
  | pctQuotedSpread | effectiveOverQuoted | pctRealized15s
  | pctRealized1m | executionSpeed
  deriving DecidableEq, Repr

def orderTypes605 : List OrderType605 :=
  [.market, .marketableLimit, .marketableIOC, .midpointBetter,
   .midpointBetterIOC, .executableNonmarketable, .executableNonmarketableIOC,
   .executableStopMarket, .executableStopMarketableLimit,
   .executableStopNonmarketableLimit]

def coreFields605 : List CoreField605 :=
  [.orderCount, .notional, .shares, .cancelled, .localExecution, .awayExecution,
   .speedLt100us, .speed100us1ms, .speed1ms10ms, .speed10ms1s,
   .speed1s10s, .speed10s30s, .speed30s5m, .speedGe5m,
   .realized50ms, .pctRealized50ms, .realized1s, .pctRealized1s,
   .realized15s, .pctRealized15s, .realized1m, .pctRealized1m,
   .realized5m, .pctRealized5m, .midpoint]

def immediateFields605 : List ImmediateField605 :=
  [.quotedSpread, .effectiveSpread, .pctEffectiveSpread, .effectiveOverQuoted,
   .improvedShares, .improvementAmount, .improvementTime, .atQuoteShares,
   .atQuoteTime, .outsideQuoteShares, .outsideQuoteAmount, .outsideQuoteTime,
   .betterDisplayedShares, .betterDisplayedAmount, .atBestDisplayedShares,
   .outsideBestDisplayedShares, .outsideBestDisplayedAmount,
   .orderSizeBenchmark, .benchmarkExcess]

/-- Fields specifically tied to the best available displayed price. The SEC
    staff FAQ gives these a November 1, 2026 compliance date. -/
def bestDisplayedFields605 : List ImmediateField605 :=
  [.betterDisplayedShares, .betterDisplayedAmount, .atBestDisplayedShares,
   .outsideBestDisplayedShares, .outsideBestDisplayedAmount]

/-- Immediate fields required during August--October 2026, before the separate
    best-available-displayed-price compliance date. -/
def septemberImmediateFields605 : List ImmediateField605 :=
  [.quotedSpread, .effectiveSpread, .pctEffectiveSpread, .effectiveOverQuoted,
   .improvedShares, .improvementAmount, .improvementTime, .atQuoteShares,
   .atQuoteTime, .outsideQuoteShares, .outsideQuoteAmount, .outsideQuoteTime,
   .orderSizeBenchmark, .benchmarkExcess]

def requiredImmediateFields605 : Rule605Profile → List ImmediateField605
  | .augustThroughOctober2026 => septemberImmediateFields605
  | .november2026AndLater => immediateFields605

def nonmarketableFields605 : List NonmarketableField605 :=
  [.filledOrders, .executableMarketShares, .executableExchangeShares, .executionTime]

def summaryFields605 : List SummaryField605 :=
  [.averageShares, .averageNotional, .midpoint, .pctQuoteOrBetter,
   .pctImproved, .weightedPctImprovement, .pctEffectiveSpread,
   .pctQuotedSpread, .effectiveOverQuoted, .pctRealized15s,
   .pctRealized1m, .executionSpeed]

structure Rule605Report where
  reportingProfile : Rule605Profile
  monthly : Bool
  electronic : Bool
  categorizedBySecurityTypeSize : Bool
  separateSingleDealerSystem : Bool
  separateAtsOperator : Bool
  hasOrderType : OrderType605 → Bool
  hasCore : CoreField605 → Bool
  hasImmediate : ImmediateField605 → Bool
  hasNonmarketable : NonmarketableField605 → Bool
  hasSummary : SummaryField605 → Bool
  sAndPAndOtherSections : Bool
  currentCsvSchemaAndRenderer : Bool
  effectiveJointPlan : Bool
  uniformPublicAccess : Bool
  fallbackMachineReadableWebsite : Bool
  retainedThreeYears : Bool
  publishedWithinOneMonth : Bool
  thresholdAndReportingPeriodApplied : Bool
  order105136TreatmentApplied : Bool
  commissionExemption : ExemptionAttestation

/-- Rule 605(a)(3) is the joint-plan route; paragraph (a)(4) is the fallback
    only when no such plan is effective. -/
def publicationRoute605 (r : Rule605Report) : Bool :=
  if r.effectiveJointPlan then r.uniformPublicAccess
  else r.fallbackMachineReadableWebsite

def rule605ChecklistPasses (r : Rule605Report) : Bool :=
  validExemptionAttestation r.commissionExemption ||
    (r.monthly && r.electronic && r.categorizedBySecurityTypeSize &&
     r.separateSingleDealerSystem && r.separateAtsOperator &&
     orderTypes605.all r.hasOrderType && coreFields605.all r.hasCore &&
     (requiredImmediateFields605 r.reportingProfile).all r.hasImmediate &&
     nonmarketableFields605.all r.hasNonmarketable &&
     summaryFields605.all r.hasSummary && r.sAndPAndOtherSections &&
     r.currentCsvSchemaAndRenderer && publicationRoute605 r &&
     r.retainedThreeYears &&
     r.publishedWithinOneMonth && r.thresholdAndReportingPeriodApplied &&
     r.order105136TreatmentApplied)

/-- Dated September 5, 2026 verification: the general amended schema applies, but
    the best-available-displayed-price fields are not yet mandatory. -/
def rule605Complies (r : Rule605Report) : Bool :=
  decide (r.reportingProfile = september2026Rule605Profile) &&
    rule605ChecklistPasses r

theorem publicationRoute605_with_plan (r : Rule605Report)
    (h : r.effectiveJointPlan = true) :
    publicationRoute605 r = r.uniformPublicAccess := by
  simp [publicationRoute605, h]

theorem publicationRoute605_without_plan (r : Rule605Report)
    (h : r.effectiveJointPlan = false) :
    publicationRoute605 r = r.fallbackMachineReadableWebsite := by
  simp [publicationRoute605, h]

theorem requiredImmediateFields605_september :
    requiredImmediateFields605 september2026Rule605Profile =
      septemberImmediateFields605 := by
  rfl

theorem requiredImmediateFields605_november :
    requiredImmediateFields605 .november2026AndLater = immediateFields605 := by
  rfl

theorem rule605_full_profile_not_september2026 (r : Rule605Report)
    (h : r.reportingProfile = .november2026AndLater) :
    rule605Complies r = false := by
  simp [rule605Complies, september2026Rule605Profile, h]

theorem orderTypes605_complete (x : OrderType605) : x ∈ orderTypes605 := by
  cases x <;> decide

theorem coreFields605_complete (x : CoreField605) : x ∈ coreFields605 := by
  cases x <;> decide

theorem immediateFields605_complete (x : ImmediateField605) :
    x ∈ immediateFields605 := by
  cases x <;> decide

theorem nonmarketableFields605_complete (x : NonmarketableField605) :
    x ∈ nonmarketableFields605 := by
  cases x <;> decide

theorem summaryFields605_complete (x : SummaryField605) :
    x ∈ summaryFields605 := by
  cases x <;> decide

/-! ## Limit Up-Limit Down Plan -/

structure LuldPlanState where
  nmsStockCovered : Bool
  tierAndPriceCategoryApplied : Bool
  rollingFiveMinuteReference : Bool
  referenceChangeThresholdApplied : Bool
  percentageParametersApplied : Bool
  lateDayDoublingApplied : Bool
  bandRoundingApplied : Bool
  executionsInsideBands : Bool
  quotesInsideOrAtBands : Bool
  limitStateDeclared : Bool
  straddleStateHandled : Bool
  fifteenSecondPauseLogic : Bool
  primaryExchangePauseAndReopen : Bool
  regulatoryHaltLogic : Bool
  processorDissemination : Bool
  participantPoliciesAndSurveillance : Bool
  overnightProtectionWhenOperative : Bool
  planExemption : ExemptionAttestation
  deriving Repr

def luldPlanComplies (s : LuldPlanState) : Bool :=
  validExemptionAttestation s.planExemption ||
    (s.nmsStockCovered && s.tierAndPriceCategoryApplied &&
     s.rollingFiveMinuteReference && s.referenceChangeThresholdApplied &&
     s.percentageParametersApplied && s.lateDayDoublingApplied &&
     s.bandRoundingApplied && s.executionsInsideBands &&
     s.quotesInsideOrAtBands && s.limitStateDeclared &&
     s.straddleStateHandled && s.fifteenSecondPauseLogic &&
     s.primaryExchangePauseAndReopen && s.regulatoryHaltLogic &&
     s.processorDissemination && s.participantPoliciesAndSurveillance &&
     s.overnightProtectionWhenOperative)

theorem luld_exemption (s : LuldPlanState)
    (h : validExemptionAttestation s.planExemption = true) :
    luldPlanComplies s = true := by
  simp [luldPlanComplies, h]

/-! ## Venue rule families -/

inductive NasdaqOrderType4702 where
  | priceToComply | priceToDisplay | nonDisplayed | postOnly
  | midpointPegPostOnly | supplemental | marketMakerPeg | marketOnOpen
  | limitOnOpen | openingImbalanceOnly | marketOnClose | limitOnClose
  | imbalanceOnly | midpointExtendedLife | meloPlusCb | companyDirectListing
  | extendedTradingClose
  deriving DecidableEq, Repr

inductive NasdaqAttribute4703 where
  | timeInForce | size | price | pegging | minimumQuantity | routing
  | discretion | reserveSize | attribution | intermarketSweep | display
  | crossParticipation | tradeNow
  deriving DecidableEq, Repr

def nasdaqOrderTypes4702 : List NasdaqOrderType4702 :=
  [.priceToComply, .priceToDisplay, .nonDisplayed, .postOnly,
   .midpointPegPostOnly, .supplemental, .marketMakerPeg, .marketOnOpen,
   .limitOnOpen, .openingImbalanceOnly, .marketOnClose, .limitOnClose,
   .imbalanceOnly, .midpointExtendedLife, .meloPlusCb, .companyDirectListing,
   .extendedTradingClose]

def nasdaqAttributes4703 : List NasdaqAttribute4703 :=
  [.timeInForce, .size, .price, .pegging, .minimumQuantity, .routing,
   .discretion, .reserveSize, .attribution, .intermarketSweep, .display,
   .crossParticipation, .tradeNow]

theorem nasdaqOrderTypes4702_complete (x : NasdaqOrderType4702) :
    x ∈ nasdaqOrderTypes4702 := by
  cases x <;> decide

theorem nasdaqAttributes4703_complete (x : NasdaqAttribute4703) :
    x ∈ nasdaqAttributes4703 := by
  cases x <;> decide

structure NasdaqCrossState where
  definitionsComplete : Bool
  eligibleInterestCorrect : Bool
  imbalanceMessagesComplete : Bool
  disseminationScheduleCorrect : Bool
  priceMaximizesVolume : Bool
  priceMinimizesImbalance : Bool
  residualSideTieBreak : Bool
  referenceDistanceTieBreak : Bool
  collarsAndThresholdsApplied : Bool
  orderPriorityApplied : Bool
  uniformExecutionPrice : Bool
  officialPriceDisseminated : Bool
  luldAndHybridVariantsApplied : Bool
  contingencyProceduresApplied : Bool
  deriving Repr

def nasdaqCrossComplies (s : NasdaqCrossState) : Bool :=
  s.definitionsComplete && s.eligibleInterestCorrect &&
    s.imbalanceMessagesComplete && s.disseminationScheduleCorrect &&
    s.priceMaximizesVolume && s.priceMinimizesImbalance &&
    s.residualSideTieBreak && s.referenceDistanceTieBreak &&
    s.collarsAndThresholdsApplied && s.orderPriorityApplied &&
    s.uniformExecutionPrice && s.officialPriceDisseminated &&
    s.luldAndHybridVariantsApplied && s.contingencyProceduresApplied

structure VenueBookState where
  sessionEligibility : Bool
  orderTypeSemantics : Bool
  attributeCompatibility : Bool
  regNmsRepricing : Bool
  regShoRepricing : Bool
  newTimestampWhenRequired : Bool
  sizeDecreaseRetainsTimestamp : Bool
  sellDesignationRetainsTimestamp : Bool
  priceDisplayTimePriority : Bool
  displayedBeforeNondisplayed : Bool
  routingInstructions : Bool
  marketDataSourceAndFallback : Bool
  noLockCrossPolicies : Bool
  selfHelpPolicies : Bool
  cancellationAndReentry : Bool
  deriving Repr

def venueBookComplies (s : VenueBookState) : Bool :=
  s.sessionEligibility && s.orderTypeSemantics && s.attributeCompatibility &&
    s.regNmsRepricing && s.regShoRepricing && s.newTimestampWhenRequired &&
    s.sizeDecreaseRetainsTimestamp && s.sellDesignationRetainsTimestamp &&
    s.priceDisplayTimePriority && s.displayedBeforeNondisplayed &&
    s.routingInstructions && s.marketDataSourceAndFallback &&
    s.noLockCrossPolicies && s.selfHelpPolicies && s.cancellationAndReentry

structure NyseAuctionState where
  generalDefinitions : Bool
  dmmResponsibilities : Bool
  floorBrokerResponsibilities : Bool
  orderEligibility : Bool
  entryModificationCancellationWindows : Bool
  imbalancePublication : Bool
  referencePrice : Bool
  collars : Bool
  freezePeriod : Bool
  priceDetermination : Bool
  allocationPriority : Bool
  dmmFacilitation : Bool
  reopeningAndHaltAuction : Bool
  contingencyProcedures : Bool
  deriving Repr

def nyseAuctionComplies (s : NyseAuctionState) : Bool :=
  s.generalDefinitions && s.dmmResponsibilities && s.floorBrokerResponsibilities &&
    s.orderEligibility && s.entryModificationCancellationWindows &&
    s.imbalancePublication && s.referencePrice && s.collars && s.freezePeriod &&
    s.priceDetermination && s.allocationPriority && s.dmmFacilitation &&
    s.reopeningAndHaltAuction && s.contingencyProcedures

/-! ## Dated clause traceability ledger -/

def clauseCorpus : List ClauseSpec := [
  ⟨.sec600, "600(b) incorporated definitions excluding (89)(i)(F) and (93)", .definition,
    destination "federal checklist predicates"
      (rule610Complies, rule611Complies, rule612Complies,
       rule201Complies, rule605Complies)⟩,
  ⟨.sec600, "600(b)(89)(i)(F) minimum-pricing-increment indicator and June 2026 relief", .definition,
    destination "MinimumIncrementIndicatorProfile600/september2026MinimumIncrementIndicatorProfile600"
      (MinimumIncrementIndicatorProfile600.june2026Relief,
       september2026MinimumIncrementIndicatorProfile600)⟩,
  ⟨.sec600, "600(b)(93) round-lot definition", .numeric,
    destination "checkedRoundLotSize600/roundLotSize600"
      (checkedRoundLotSize600, roundLotSize600)⟩,
  ⟨.sec610, "610(a)", .procedure,
    destination "Rule610State.fairSroTradingAccess"
      Rule610State.fairSroTradingAccess⟩,
  ⟨.sec610, "610(b)(1)", .procedure,
    destination "Rule610State.equivalentDisplayOnlyAccess"
      Rule610State.equivalentDisplayOnlyAccess⟩,
  ⟨.sec610, "610(b)(2)", .procedure,
    destination "Rule610State.fairDisplayOnlyAccess"
      Rule610State.fairDisplayOnlyAccess⟩,
  ⟨.sec610, "610(c)(1)-(2)", .numeric,
    destination "FeeProfile610/accessFeeCap610"
      (september2026FeeProfile610, accessFeeCap610)⟩,
  ⟨.sec610, "610(d)", .disclosure,
    destination "Rule610State.feeKnownAtExecution"
      Rule610State.feeKnownAtExecution⟩,
  ⟨.sec610, "610(e)(1)(i)-(ii)", .procedure,
    destination "Rule610State lock-avoidance fields"
      (Rule610State.avoidsProtectedLocks, Rule610State.avoidsManualLocks)⟩,
  ⟨.sec610, "610(e)(2)-(3)", .procedure,
    destination "Rule610State reconciliation and pattern fields"
      (Rule610State.reconcilesLocks, Rule610State.noLockPattern)⟩,
  ⟨.sec610, "610(f)", .exception,
    destination "Rule610State.commissionExemption/validExemptionAttestation"
      (Rule610State.commissionExemption, validExemptionAttestation)⟩,
  ⟨.sec611, "611(a)(1)", .procedure,
    destination "Rule611State.writtenPolicies" Rule611State.writtenPolicies⟩,
  ⟨.sec611, "611(a)(2)", .procedure,
    destination "Rule611State surveillance and remediation fields"
      (Rule611State.regularSurveillance, Rule611State.promptRemediation)⟩,
  ⟨.sec611, "611(b)(1)-(9)", .exception,
    destination "Rule611Exception/validRule611Exception"
      (validRule611Exception, rule611TransactionAllowed)⟩,
  ⟨.sec611, "611(b)(9)(i)-(iii)", .exception,
    destination "Rule611ExceptionFacts stopped-order fields"
      (Rule611ExceptionFacts.stoppedCustomer,
       Rule611ExceptionFacts.stoppedCustomerAgreed,
       Rule611ExceptionFacts.stoppedPriceCondition)⟩,
  ⟨.sec611, "611(c)", .procedure,
    destination "Rule611State.reasonableISOSteps" Rule611State.reasonableISOSteps⟩,
  ⟨.sec611, "611(d)", .exception,
    destination "Rule611State.commissionExemption/validExemptionAttestation"
      (Rule611State.commissionExemption, validExemptionAttestation)⟩,
  ⟨.sec612, "612(a)(1)(i)-(ii)", .definition,
    destination "EvaluationPeriod612" operativePeriodFor612⟩,
  ⟨.sec612, "612(a)(2)", .definition,
    destination "Rule612State.twaSpread" Rule612State.twaSpread⟩,
  ⟨.sec612, "612(b)(1)(i)-(ii)", .stateTransition,
    destination "operativePeriodFor612/rule612SchedulePasses"
      (operativePeriodFor612, rule612SchedulePasses)⟩,
  ⟨.sec612, "612(b)(2)(i)-(ii)", .numeric,
    destination "PricingProfile612/minimumTick612"
      (september2026PricingProfile612, minimumTick612)⟩,
  ⟨.sec612, "612(b)(3)", .numeric,
    destination "minimumTick612 subdollar branches"
      (minimumTick612, rule612PriceComplies)⟩,
  ⟨.sec612, "612(c)", .numeric,
    destination "minimumTick612_amended_new_stock"
      minimumTick612⟩,
  ⟨.sec612, "612(d)", .exception,
    destination "Rule612State.commissionExemption/validExemptionAttestation"
      (Rule612State.commissionExemption, validExemptionAttestation)⟩,
  ⟨.regSho201, "201(a)(1)-(9)", .definition,
    destination "Rule201State/ShortExemptFacts201 projections"
      (Rule201State.coveredSecurity, ShortExemptFacts201.aboveNbbAtSubmission)⟩,
  ⟨.regSho201, "201(b)(1)(i)-(iii)", .stateTransition,
    destination "restrictionApplies201/transactionAllowed201"
      (restrictionApplies201, transactionAllowed201)⟩,
  ⟨.regSho201, "201(b)(2)-(3)", .procedure,
    destination "Rule201State surveillance, determination, and notice fields"
      (Rule201State.tradingCenterSurveillance,
       Rule201State.listingMarketDetermined, Rule201State.listingMarketNotified)⟩,
  ⟨.regSho201, "201(c)(1)-(2)", .procedure,
    destination "validShortExempt201 above-NBB branch"
      (validShortExempt201, ShortExemptFacts201.aboveNbbAtSubmission)⟩,
  ⟨.regSho201, "201(d)(1)-(5)", .exception,
    destination "ShortExemptReason201 paragraphs (d)(1)-(5)"
      (ShortExemptReason201.ownerDeliveryRestriction,
       ShortExemptReason201.oddLotMarketMaker,
       ShortExemptReason201.convertibleArbitrage,
       ShortExemptReason201.foreignArbitrage,
       ShortExemptReason201.underwriterOverallotment,
       ShortExemptReason201.underwriterLayoff)⟩,
  ⟨.regSho201, "201(d)(6)(i)-(iii)", .exception,
    destination "validShortExempt201 riskless-principal fields"
      (ShortExemptReason201.risklessPrincipal,
       ShortExemptFacts201.customerOrderFirst,
       ShortExemptFacts201.allocationWithin60Seconds,
       ShortExemptFacts201.timeSequencedRecords)⟩,
  ⟨.regSho201, "201(d)(7)(i)-(v)", .exception,
    destination "validShortExempt201 VWAP fields"
      (ShortExemptReason201.vwap, ShortExemptFacts201.vwapEveryRegularWayTrade,
       ShortExemptFacts201.vwapAggregateAndDivide,
       ShortExemptFacts201.noManipulativePurpose)⟩,
  ⟨.regSho201, "201(e)", .procedure,
    destination "Rule201State.sroRuleConforming" Rule201State.sroRuleConforming⟩,
  ⟨.regSho201, "201(f)", .exception,
    destination "Rule201State.commissionExemption/validExemptionAttestation"
      (Rule201State.commissionExemption, validExemptionAttestation)⟩,
  ⟨.sec605, "605(a)(1) order classes", .definition,
    destination "orderTypes605" orderTypes605⟩,
  ⟨.sec605, "605(a)(1)(i)(A)-(Y)", .disclosure,
    destination "coreFields605" coreFields605⟩,
  ⟨.sec605, "605(a)(1)(ii)(A)-(S)", .disclosure,
    destination "immediateFields605" immediateFields605⟩,
  ⟨.sec605, "Rule 605 FAQ 39 (Nov. 1, 2026 compliance date)", .procedure,
    destination "Rule605Profile/requiredImmediateFields605"
      (september2026Rule605Profile, requiredImmediateFields605,
       bestDisplayedFields605)⟩,
  ⟨.sec605, "605(a)(1)(iii)(A)-(D)", .disclosure,
    destination "nonmarketableFields605" nonmarketableFields605⟩,
  ⟨.sec605, "605(a)(2)(i)-(xii)", .disclosure,
    destination "summaryFields605" summaryFields605⟩,
  ⟨.sec605, "605(a)(3)-(6)", .procedure,
    destination "publicationRoute605 and publication/retention fields"
      (publicationRoute605, Rule605Report.retainedThreeYears,
       Rule605Report.publishedWithinOneMonth)⟩,
  ⟨.sec605, "605(a)(7)", .procedure,
    destination "Rule605Report.thresholdAndReportingPeriodApplied"
      Rule605Report.thresholdAndReportingPeriodApplied⟩,
  ⟨.sec605, "Exchange Act Release 34-105136 Sections II.A-II.B", .exception,
    destination "Rule605Report.order105136TreatmentApplied"
      Rule605Report.order105136TreatmentApplied⟩,
  ⟨.sec605, "605(b)", .exception,
    destination "Rule605Report.commissionExemption/validExemptionAttestation"
      (Rule605Report.commissionExemption, validExemptionAttestation)⟩,
  ⟨.luld, "Plan I-II", .definition,
    destination "LuldPlanState coverage and tier fields"
      (LuldPlanState.nmsStockCovered, LuldPlanState.tierAndPriceCategoryApplied)⟩,
  ⟨.luld, "Plan III-IV", .numeric,
    destination "LuldPlanState reference, percentage, and rounding fields"
      (LuldPlanState.rollingFiveMinuteReference,
       LuldPlanState.percentageParametersApplied, LuldPlanState.bandRoundingApplied)⟩,
  ⟨.luld, "Plan V-VI", .stateTransition,
    destination "LuldPlanState band, state, and pause fields"
      (LuldPlanState.executionsInsideBands, LuldPlanState.limitStateDeclared,
       LuldPlanState.straddleStateHandled, LuldPlanState.fifteenSecondPauseLogic)⟩,
  ⟨.luld, "Plan VII-VIII", .procedure,
    destination "LuldPlanState reopen and halt fields"
      (LuldPlanState.primaryExchangePauseAndReopen, LuldPlanState.regulatoryHaltLogic)⟩,
  ⟨.luld, "Plan IX-XI and amendments", .procedure,
    destination "LuldPlanState dissemination, policy, overnight, and relief fields"
      (LuldPlanState.processorDissemination,
       LuldPlanState.participantPoliciesAndSurveillance,
       LuldPlanState.overnightProtectionWhenOperative, LuldPlanState.planExemption)⟩,
  ⟨.nyse731, "NYSE 7.31(a)-(i)", .stateTransition,
    destination "VenueBookState order-type and modifier fields"
      (VenueBookState.orderTypeSemantics, VenueBookState.attributeCompatibility)⟩,
  ⟨.nyse735, "NYSE 7.35 general/A/B", .stateTransition,
    destination "NyseAuctionState/nyseAuctionComplies" nyseAuctionComplies⟩,
  ⟨.nyse737, "NYSE 7.37(a)-(g)", .stateTransition,
    destination "VenueBookState/rule737full/matchNYSE"
      (venueBookComplies, rule737full, matchNYSE)⟩,
  ⟨.nasdaq4702, "Nasdaq 4702(a)", .procedure,
    destination "VenueBookState session and protocol fields"
      (VenueBookState.sessionEligibility, VenueBookState.routingInstructions)⟩,
  ⟨.nasdaq4702, "Nasdaq 4702(b)(1)-(17)", .stateTransition,
    destination "nasdaqOrderTypes4702" nasdaqOrderTypes4702⟩,
  ⟨.nasdaq4703, "Nasdaq 4703(a)-(m)", .stateTransition,
    destination "nasdaqAttributes4703" nasdaqAttributes4703⟩,
  ⟨.nasdaq4752, "Nasdaq 4752(a)-(d)", .stateTransition,
    destination "NasdaqCrossState/nasdaqCrossComplies" nasdaqCrossComplies⟩,
  ⟨.nasdaq4753, "Nasdaq 4753(a)-(e)", .stateTransition,
    destination "NasdaqCrossState halt-cross and LULD fields"
      (NasdaqCrossState.luldAndHybridVariantsApplied,
       NasdaqCrossState.contingencyProceduresApplied)⟩,
  ⟨.nasdaq4754, "Nasdaq 4754(a)-(b)", .stateTransition,
    destination "NasdaqCrossState/nasdaqCrossComplies" nasdaqCrossComplies⟩,
  ⟨.nasdaq4757, "Nasdaq 4757(a)-(c)", .stateTransition,
    destination "VenueBookState price/display/time fields"
      (VenueBookState.priceDisplayTimePriority,
       VenueBookState.displayedBeforeNondisplayed,
       VenueBookState.newTimestampWhenRequired)⟩
]

def clauseMapped (c : ClauseSpec) : Bool :=
  decide (0 < c.citation.length ∧ 0 < c.destination.name.length)

def clauseCount (r : CorpusRule) : Nat :=
  (clauseCorpus.filter (fun c => c.rule == r)).length

/-- The ledger has 58 expressly cited paragraph, paragraph-range, FAQ, or
    exemptive-order entries. -/
theorem clause_corpus_has_58_entries : clauseCorpus.length = 58 := by
  rfl

/-- The fixed corpus has no ledger entry without source and destination labels;
    construction separately requires an elaborated destination object.  This is
    a traceability theorem, not a legal conclusion about supplied evidence. -/
theorem clause_corpus_traceability_complete :
    clauseCorpus.all clauseMapped = true := by
  rfl

/-- Duplicate citations cannot silently collapse two ledger rows. -/
theorem clause_corpus_citations_unique :
    (clauseCorpus.map ClauseSpec.citation).Nodup := by
  decide +revert

/-- The advertised family breakdown is itself checked against the ledger. -/
theorem clause_corpus_family_counts :
    clauseCount .sec600 = 3 ∧ clauseCount .sec605 = 10 ∧
    clauseCount .sec610 = 8 ∧ clauseCount .sec611 = 6 ∧
    clauseCount .sec612 = 7 ∧ clauseCount .regSho201 = 9 ∧
    clauseCount .luld = 5 ∧ clauseCount .nyse731 = 1 ∧
    clauseCount .nyse735 = 1 ∧ clauseCount .nyse737 = 1 ∧
    clauseCount .nasdaq4702 = 2 ∧ clauseCount .nasdaq4703 = 1 ∧
    clauseCount .nasdaq4752 = 1 ∧ clauseCount .nasdaq4753 = 1 ∧
    clauseCount .nasdaq4754 = 1 ∧
    clauseCount .nasdaq4757 = 1 := by
  decide +revert

end Rule737
