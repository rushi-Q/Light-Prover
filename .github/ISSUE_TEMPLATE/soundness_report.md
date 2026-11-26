---
name: Soundness concern (non-sensitive)
about: Questions or gaps in the soundness argument, trust model or documentation that are NOT an exploitable false accept
title: "[soundness] "
labels: soundness
---

<!--
READ FIRST: if you have found (or suspect) any of the following, do NOT use this public template. Report it privately
through GitHub private vulnerability reporting as described in SECURITY.md:

  * a false ACCEPTED (or a false CONDITIONAL) with trust `sound`, `sound-conditional` or `notary`, including the
    low-memory, ultra-low-memory and Lean 4.37 judges;
  * a sandbox escape of untrusted project code;
  * any way to change a verdict, an exit status or result.json without the trusted check deciding it (cache or daemon
    poisoning, bypassing the challenge pin or the binary pins, trust parameters smuggled through a request).

Use this template for everything else about soundness, for example: an unclear or missing step in a soundness
argument, a trusted component that is not covered by the gates, a documentation statement about guarantees that looks
wrong, or behaviour of UNSAFE / research presets that are documented as not sound.
-->

## Concern

<!-- What part of the soundness argument, trust model or documentation is affected, and why. -->

## Where

<!-- Files, documents or components (e.g. docs/soundness.md section 1, fastverify/check/sound/README.md). -->

## Suggested resolution

<!-- Optional: a fix, an extra gate or test, or a documentation change. -->

## Confirmation

- [ ] This is not an exploitable false ACCEPTED, sandbox escape or verdict tampering (those go to SECURITY.md).
