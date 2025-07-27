# Component Architecture

This directory contains all React components organized into logical categories for better maintainability, debuggability, and interpretability for both humans and LLMs.

## Directory Structure

```
components/
├── dashboard/          # Dashboard-specific components
│   ├── ClassHealthCard.tsx
│   ├── QuickStatsPanel.tsx
│   └── index.ts
├── chat/              # Chat and communication components
│   ├── ChatMentor.tsx
│   └── index.ts
├── learning/          # Learning and educational components
│   ├── StudentMasteryPanel.tsx
│   ├── StudentKnowledgeVector.tsx
│   └── index.ts
├── visualization/     # Data visualization components
│   ├── KnowledgeGraph.tsx
│   ├── AdjacencyMatrix.tsx
│   └── index.ts
├── common/           # Shared utility components
│   ├── Katex.tsx
│   ├── ViewModeSwitcher.tsx
│   └── index.ts
├── index.ts          # Main export file
└── README.md         # This file
```

## Import Patterns

### Recommended (Clean imports)
```typescript
import { ClassHealthCard, QuickStatsPanel } from '../components';
import { ChatMentor } from '../components';
import { KnowledgeGraph } from '../components';
```

### Category-specific imports (if needed)
```typescript
import { ClassHealthCard } from '../components/dashboard';
import { ChatMentor } from '../components/chat';
```

## Component Categories

### Dashboard Components (`/dashboard`)
- **ClassHealthCard**: Visual representation of class health with plant states
- **QuickStatsPanel**: Overview statistics display

### Chat Components (`/chat`)
- **ChatMentor**: Main chat interface with AI tutor

### Learning Components (`/learning`)
- **StudentMasteryPanel**: Student knowledge state management
- **StudentKnowledgeVector**: Knowledge vector visualization

### Visualization Components (`/visualization`)
- **KnowledgeGraph**: D3.js knowledge graph visualization
- **AdjacencyMatrix**: Matrix representation of concept relationships

### Common Components (`/common`)
- **Katex**: Mathematical notation rendering
- **ViewModeSwitcher**: Navigation between different views

## Design Principles

1. **Single Responsibility**: Each component has one clear purpose
2. **Modularity**: Components are organized by function
3. **Reusability**: Common components can be used across the app
4. **Type Safety**: All components use TypeScript interfaces
5. **Consistent Naming**: Components follow PascalCase naming
6. **Clean Imports**: Index files enable clean import statements

## Adding New Components

1. **Choose the appropriate category** based on the component's function
2. **Create the component file** in the relevant subdirectory
3. **Add the export** to the category's `index.ts` file
4. **Update this README** if adding a new category

## Benefits for LLMs and Humans

- **Clear Organization**: Easy to understand component relationships
- **Predictable Structure**: Consistent file organization
- **Self-Documenting**: Category names indicate component purpose
- **Maintainable**: Changes are isolated to relevant categories
- **Debuggable**: Easy to locate and fix issues 