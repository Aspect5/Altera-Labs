import React, { useEffect, useRef } from 'react';

// KaTeX is loaded globally via a <script> tag in index.html, so we declare it here.
declare const katex: {
  render(expression: string, element: HTMLElement, options?: {
    displayMode?: boolean;
    throwOnError?: boolean;
  }): void;
};

interface KatexProps {
  math: string;
  block?: boolean;
}

const Katex: React.FC<KatexProps> = ({ math, block = false }) => {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    // The `katex` object is attached to the window object by the script loaded in index.html.
    if (ref.current && typeof katex !== 'undefined') {
      // The original error was a ParseError from KaTeX about quirks mode.
      // This new loading strategy (via <script>) should resolve the environment issue.
      // We keep `throwOnError: false` to gracefully handle malformed math expressions.
      katex.render(math, ref.current, {
        throwOnError: false,
        displayMode: block,
      });
    }
  }, [math, block]);

  return <span ref={ref} />;
};

export default Katex;