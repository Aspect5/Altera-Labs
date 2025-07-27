# Frontend Architecture

This document describes the modular architecture of the Altera Labs frontend, designed for maintainability, debuggability, and interpretability for both humans and LLMs.

## Project Structure

```
frontend/
├── components/           # React components (modular)
│   ├── dashboard/       # Dashboard-specific components
│   ├── chat/           # Chat and communication
│   ├── learning/       # Educational components
│   ├── visualization/  # Data visualization
│   ├── common/         # Shared utilities
│   └── index.ts        # Main component exports
├── services/           # API and business logic
│   ├── aiService.ts    # AI and chat services
│   ├── dashboardService.ts # Dashboard data
│   ├── bayesianService.ts  # BKT services
│   └── index.ts        # Main service exports
├── src/
│   └── pages/          # Page components
│       ├── DashboardPage.tsx
│       ├── TutorPage.tsx
│       └── SetupPage.tsx
├── types.ts            # TypeScript type definitions
├── App.tsx             # Main application component
├── index.tsx           # Application entry point
└── ARCHITECTURE.md     # This file
```

## Design Principles

### 1. Modularity
- **Component Categories**: Components are organized by function
- **Service Separation**: Business logic separated from UI components
- **Type Safety**: Comprehensive TypeScript interfaces

### 2. Clean Imports
```typescript
// ✅ Recommended
import { ClassHealthCard, QuickStatsPanel } from '../components';
import { dashboardService } from '../services';

// ❌ Avoid
import ClassHealthCard from '../components/dashboard/ClassHealthCard';
import { dashboardService } from '../services/dashboardService';
```

### 3. Single Responsibility
- Each component has one clear purpose
- Services handle specific domains (AI, dashboard, BKT)
- Pages orchestrate components and state

### 4. Consistent Patterns
- All components use TypeScript interfaces
- Consistent naming conventions (PascalCase for components)
- Standardized prop patterns

## Component Architecture

### Dashboard Components
- **ClassHealthCard**: Visual class health indicators
- **QuickStatsPanel**: Overview statistics

### Chat Components  
- **ChatMentor**: Main AI chat interface

### Learning Components
- **StudentMasteryPanel**: Knowledge state management
- **StudentKnowledgeVector**: Knowledge visualization

### Visualization Components
- **KnowledgeGraph**: D3.js graph visualization
- **AdjacencyMatrix**: Matrix representation

### Common Components
- **Katex**: Mathematical notation
- **ViewModeSwitcher**: Navigation controls

## Service Architecture

### AI Service (`aiService.ts`)
- Chat message handling
- Session management
- Proof verification
- Class creation

### Dashboard Service (`dashboardService.ts`)
- Class data retrieval
- Statistics calculation
- Session updates

### Bayesian Service (`bayesianService.ts`)
- Knowledge state management
- BKT calculations
- Learning analytics

## State Management

### App-Level State (App.tsx)
- Global application state
- Navigation state
- Session management
- Dashboard data

### Component-Level State
- Local UI state
- Form data
- Component-specific logic

## Data Flow

1. **User Action** → Component
2. **Component** → Service (API call)
3. **Service** → Backend
4. **Backend** → Service (response)
5. **Service** → Component (data update)
6. **Component** → UI (re-render)

## Benefits for Development

### For Humans
- **Clear Organization**: Easy to find and understand code
- **Predictable Structure**: Consistent file organization
- **Maintainable**: Changes are isolated to relevant areas
- **Debuggable**: Clear separation of concerns

### For LLMs
- **Self-Documenting**: Structure indicates purpose
- **Consistent Patterns**: Predictable code organization
- **Modular Design**: Easy to understand component relationships
- **Type Safety**: Clear interfaces and contracts

## Adding New Features

1. **Identify Category**: Choose appropriate component/service category
2. **Create Component**: Add to relevant subdirectory
3. **Update Exports**: Add to category index.ts
4. **Add Types**: Update types.ts if needed
5. **Update Documentation**: Modify this file if adding new categories

## Testing Strategy

- **Component Tests**: Test individual components
- **Service Tests**: Test API integration
- **Integration Tests**: Test component interactions
- **E2E Tests**: Test complete user flows

## Performance Considerations

- **Lazy Loading**: Components loaded on demand
- **Memoization**: React.memo for expensive components
- **Service Caching**: API response caching
- **Bundle Splitting**: Code splitting by routes 