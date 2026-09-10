/** Exact rationals over BigInt. Always normalized: den > 0, gcd(num, den) = 1. */
export class Rational {
  readonly num: bigint;
  readonly den: bigint;
  /**
   * Mathematica-style "approximate" flag: set by decimal literals and N(). Approximate numbers
   * print as decimals; exact ones as fractions. The flag is contagious through arithmetic.
   */
  readonly approx: boolean;

  private constructor(num: bigint, den: bigint, approx = false) { this.num = num; this.den = den; this.approx = approx; }

  static of(num: bigint | number, den: bigint | number = 1n, approx = false): Rational {
    let n = BigInt(num), d = BigInt(den);
    if (d === 0n) throw new Error("division by zero");
    if (d < 0n) { n = -n; d = -d; }
    const g = gcd(n < 0n ? -n : n, d);
    return new Rational(n / g, d / g, approx);
  }
  withApprox(approx: boolean): Rational { return new Rational(this.num, this.den, approx); }
  static readonly ZERO = Rational.of(0);
  static readonly ONE = Rational.of(1);
  static readonly MINUS_ONE = Rational.of(-1);

  /** Parse "3", "-7", "2.5", "1/3". Decimal literals are stored exactly (2.5 = 5/2) but flagged approximate. */
  static parse(s: string): Rational {
    const frac = s.split("/");
    if (frac.length === 2) return Rational.of(BigInt(frac[0]!), BigInt(frac[1]!));
    const [intPart, decPart] = s.split(".");
    if (decPart === undefined) return Rational.of(BigInt(intPart!));
    const scale = 10n ** BigInt(decPart.length);
    return Rational.of(BigInt((intPart || "0") + decPart), scale, true);
  }

  add(o: Rational): Rational { return Rational.of(this.num * o.den + o.num * this.den, this.den * o.den, this.approx || o.approx); }
  sub(o: Rational): Rational { return this.add(o.neg()); }
  mul(o: Rational): Rational { return Rational.of(this.num * o.num, this.den * o.den, this.approx || o.approx); }
  div(o: Rational): Rational { return Rational.of(this.num * o.den, this.den * o.num, this.approx || o.approx); }
  neg(): Rational { return new Rational(-this.num, this.den, this.approx); }
  inv(): Rational { return Rational.of(this.den, this.num, this.approx); }
  pow(n: bigint): Rational {
    if (n < 0n) return this.inv().pow(-n);
    return Rational.of(this.num ** n, this.den ** n, this.approx);
  }

  isZero(): boolean { return this.num === 0n; }
  isOne(): boolean { return this.num === 1n && this.den === 1n; }
  isInteger(): boolean { return this.den === 1n; }
  isNegative(): boolean { return this.num < 0n; }
  eq(o: Rational): boolean { return this.num === o.num && this.den === o.den; }
  cmp(o: Rational): number { const d = this.num * o.den - o.num * this.den; return d < 0n ? -1 : d > 0n ? 1 : 0; }

  toNumber(): number { return Number(this.num) / Number(this.den); }
  /** Decimal expansion to 15 significant digits (only used for approximate numbers). */
  private decimal(): string {
    const s = this.toNumber().toPrecision(15);
    return s.includes("e") ? s : s.replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
  }
  toString(): string { return this.approx ? this.decimal() : this.den === 1n ? this.num.toString() : `${this.num}/${this.den}`; }
  toLatex(): string {
    if (this.den === 1n) return this.num.toString();
    if (this.approx) return this.decimal();
    const sign = this.num < 0n ? "-" : "";
    return `${sign}\\frac{${this.num < 0n ? -this.num : this.num}}{${this.den}}`;
  }
}

export function gcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) { [a, b] = [b, a % b]; }
  return a === 0n ? 1n : a;
}
