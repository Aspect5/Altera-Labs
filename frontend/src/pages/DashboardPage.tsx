import React from 'react';
import { ClassSummary, QuickStats } from '../../types/components';
import { ClassHealthCard, QuickStatsPanel } from '../../components';
import { dashboardService } from '../../services';

interface DashboardPageProps {
  classes: ClassSummary[];
  stats: QuickStats;
  onCreateClass: () => void;
  onSelectClass: (classId: string) => void;
  isLoading?: boolean;
  error?: string | null;
}

const DashboardPage: React.FC<DashboardPageProps> = ({
  classes,
  stats,
  onCreateClass,
  onSelectClass,
  isLoading = false,
  error = null,
}) => {
  // Show loading state
  if (isLoading) {
    return (
      <div className="max-w-7xl mx-auto space-y-8">
        <div className="text-center">
          <h1 className="text-3xl font-bold text-blue-400 mb-2">
            Your Learning Dashboard
          </h1>
          <p className="text-slate-400">
            Track your progress and continue your learning journey
          </p>
        </div>
        <div className="flex items-center justify-center py-12">
          <div className="text-center">
            <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-400 mx-auto mb-4"></div>
            <p className="text-slate-400">Loading your learning data...</p>
          </div>
        </div>
      </div>
    );
  }

  // Show error state
  if (error) {
    return (
      <div className="max-w-7xl mx-auto space-y-8">
        <div className="text-center">
          <h1 className="text-3xl font-bold text-blue-400 mb-2">
            Your Learning Dashboard
          </h1>
          <p className="text-slate-400">
            Track your progress and continue your learning journey
          </p>
        </div>
        <div className="bg-red-900/20 border border-red-700 rounded-lg p-6 text-center">
          <div className="text-red-400 text-lg font-semibold mb-2">Error Loading Dashboard</div>
          <p className="text-slate-400 mb-4">{error}</p>
          <button
            onClick={() => window.location.reload()}
            className="px-4 py-2 bg-red-600 hover:bg-red-500 text-white rounded-lg transition-colors"
          >
            Try Again
          </button>
        </div>
      </div>
    );
  }

  return (
    <div className="max-w-7xl mx-auto space-y-8">
      {/* Header */}
      <div className="text-center">
        <h1 className="text-3xl font-bold text-blue-400 mb-2">
          Your Learning Dashboard
        </h1>
        <p className="text-slate-400">
          Track your progress and continue your learning journey
        </p>
      </div>

      {/* Quick Stats Panel */}
      <QuickStatsPanel stats={stats} />

      {/* Classes Section */}
      <div className="space-y-6">
        <div className="flex items-center justify-between">
          <h2 className="text-2xl font-semibold text-slate-200">
            Your Classes
          </h2>
          <button
            onClick={onCreateClass}
            className="px-6 py-3 bg-blue-600 hover:bg-blue-700 text-white font-medium rounded-lg transition-colors duration-200 flex items-center gap-2"
          >
            <span className="text-lg">+</span>
            Add New Class
          </button>
        </div>

        {classes.length === 0 ? (
          <div className="bg-slate-800 rounded-lg p-12 text-center border border-slate-700">
            <div className="text-6xl mb-4">🌱</div>
            <h3 className="text-xl font-semibold text-slate-200 mb-2">
              No Classes Yet
            </h3>
            <p className="text-slate-400 mb-6">
              Create your first class to start your learning journey
            </p>
            <button
              onClick={onCreateClass}
              className="px-6 py-3 bg-blue-600 hover:bg-blue-700 text-white font-medium rounded-lg transition-colors duration-200"
            >
              Create Your First Class
            </button>
          </div>
        ) : (
          <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
            {classes.map((classData) => (
              <ClassHealthCard
                key={classData.id}
                classData={classData}
                onClick={() => onSelectClass(classData.id)}
                onDelete={async (id) => {
                  try {
                    await dashboardService.deleteClass(id);
                    window.location.reload();
                  } catch (e) {
                    alert('Failed to delete class.');
                  }
                }}
              />
            ))}
          </div>
        )}
      </div>

      {/* Recent Activity Section */}
      {classes.length > 0 && (
        <div className="space-y-4">
          <h2 className="text-2xl font-semibold text-slate-200">
            Recent Activity
          </h2>
          <div className="bg-slate-800 rounded-lg p-6 border border-slate-700">
            <div className="space-y-3">
              {classes
                .filter((classData) => classData.lastSession)
                .sort((a, b) => 
                  (b.lastSession?.getTime() || 0) - (a.lastSession?.getTime() || 0)
                )
                .slice(0, 3)
                .map((classData) => (
                  <div key={classData.id} className="flex items-center justify-between p-3 bg-slate-700 rounded-lg">
                    <div className="flex items-center gap-3">
                      <span className="text-xl">{classData.plantState === 'flourishing' ? '🌱' : '🌿'}</span>
                      <div>
                        <div className="font-medium text-slate-200">
                          {classData.name}
                        </div>
                        <div className="text-sm text-slate-400">
                          Last session: {classData.lastSession?.toLocaleDateString()}
                        </div>
                      </div>
                    </div>
                    <div className="text-sm text-slate-400">
                      {classData.conceptsMastered} concepts mastered
                    </div>
                  </div>
                ))}
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default DashboardPage; 